/*  towerofhanoi.pl  --  Tower of Hanoi web game, ONE file.
    Requires SWI-Prolog 9.x.  Run:  swipl towerofhanoi.pl   (port 8080)

    Prolog owns all game logic (validation, moves, undo, timing, par/limit,
    random picks, ranking with ties, leaderboard).  JavaScript only calls the
    endpoints below, animates and plays synthesized audio.

    JSON ENDPOINTS  (all replies are JSON; errors are {"error":Code,...})
      GET  /                      the game page (HTML+CSS+JS embedded below)
      GET  /api/modes             mode table: id, discs, par, factor, limit
      GET  /api/random-mode       {"mode":M}   Prolog picks a mode at random
      GET  /api/random-basis      {"basis":B}  "moves" or "time"
      POST /api/new               {mode:"easy|hard|difficult|nightmare|random",
                                   players:["A",..1-4 names], basis:"moves|time|random",
                                   basis_random:bool}      -> {state}
      POST /api/begin             {game}  start the timer of the current turn
      POST /api/move              {game,from,to}  towers 0..2
                                   422 {"error":"invalid_move","reason":..} if illegal
      POST /api/undo              {game}  single player only
      POST /api/restart           {game}  single player only
      POST /api/pause             {game,paused:bool}  single player only
                                   (undo/restart/pause in multiplayer: HTTP 403
                                    {"error":"not_allowed_in_multiplayer"})
      POST /api/finish            {game}  final ranking + leaderboard once all
                                   players have solved the puzzle (else 409)
      GET  /api/state?game=ID     current state
      GET  /api/leaderboard[?mode=M&basis=B]   best 10 per mode and basis

    Stop the server:  ?- stop_hanoi.   or   ?- halt.
*/

:- encoding(utf8).

% ===================================================================
% 1. LIBRARIES
% ===================================================================
:- use_module(library(http/thread_httpd)).
:- use_module(library(http/http_dispatch)).
:- use_module(library(http/http_json)).
:- use_module(library(http/http_parameters)).
:- use_module(library(http/json)).
:- use_module(library(www_browser)).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(pairs)).
:- use_module(library(random)).
:- use_module(library(quasi_quotations)).

:- dynamic game_rec/2.            % game_rec(Id, StateDict)
:- dynamic lb_entries/3.          % lb_entries(Mode, Basis, EntryDicts)
:- dynamic base_dir/1.

% remember the folder of this file (leaderboard.json lives next to it)
:- prolog_load_context(directory, D), retractall(base_dir(_)), assertz(base_dir(D)).

% {|raw||...|} : quasi quotation giving the text verbatim as a string,
% so HTML/CSS/JS can be embedded without escaping quotes or backslashes.
:- quasi_quotation_syntax(raw).
raw(Content, _Vars, _Dict, String) :-
    with_quasi_quotation_input(Content, Stream, read_string(Stream, _, String)).

server_port(8080).

% ===================================================================
% 2. CONFIGURATION  (mode, discs, limit factor)
% ===================================================================
mode_def(easy,      3, 1.5).
mode_def(hard,      5, 1.4).
mode_def(difficult, 7, 1.3).
mode_def(nightmare, 9, 1.25).

mode_numbers(Mode, N, Par, Limit) :-
    mode_def(Mode, N, Factor),
    Par is (1 << N) - 1,
    Limit is ceiling(Par * Factor).

% ===================================================================
% 3. GAME LOGIC
% Pegs are stored top-first: [[1,2,3],[],[]] (1 = smallest disc).
% The JSON sent to the browser lists each tower bottom-first.
% ===================================================================
initial_pegs(N, [Discs, [], []]) :- numlist(1, N, Discs).

solved(N, [[], [], Third]) :- length(Third, N).

stars(Moves, Par, _, 3) :- Moves =< Par * 1.1, !.
stars(Moves, _, Limit, 2) :- Moves =< Limit, !.
stars(_, _, _, 1).

set_nth0(I, L0, New, L) :- nth0(I, L0, _, Rest), nth0(I, L, New, Rest).

%   apply_move(+Pegs0, +From, +To, -Pegs, -Reason)
%   Reason is unbound when the move is legal.
check_move(Pegs0, From, To, Pegs, Reason) :-
    nth0(From, Pegs0, FromPeg),
    nth0(To, Pegs0, ToPeg),
    (   From =:= To
    ->  Reason = same_tower
    ;   FromPeg == []
    ->  Reason = empty_tower
    ;   FromPeg = [Disc|FromRest],
        ToPeg = [Top|_], Top < Disc
    ->  Reason = larger_on_smaller
    ;   FromPeg = [Disc|FromRest],
        set_nth0(From, Pegs0, FromRest, P1),
        set_nth0(To, P1, [Disc|ToPeg], Pegs)
    ).

elapsed_ms(S, Now, Ms) :-
    get_dict(acc_ms, S, Acc),
    get_dict(run_since, S, Since),
    (   number(Since) -> Ms is round(Acc + (Now - Since) * 1000) ; Ms is round(Acc) ).

%   Ranking: sort key per basis; equal PRIMARY value shares a rank (1,1,3).
primary(moves, E, V) :- get_dict(moves, E, V).
primary(time,  E, V) :- get_dict(time_s, E, V).
sort_key(moves, E, M-T) :- get_dict(moves, E, M), get_dict(time_ms, E, T).
sort_key(time,  E, T-M) :- get_dict(time_s, E, T), get_dict(moves, E, M).

sort_entries(Basis, Es0, Es) :-
    findall(K-E, (member(E, Es0), sort_key(Basis, E, K)), Ps0),
    keysort(Ps0, Ps),
    pairs_values(Ps, Es).

rank_sorted(Basis, Sorted, Ranked) :- number_ranks(Sorted, Basis, 1, none, 0, Ranked).

number_ranks([], _, _, _, _, []).
number_ranks([E|T], Basis, Pos, PrevP, PrevRank, [R|Rs]) :-
    primary(Basis, E, P),
    (   P == PrevP -> Rank = PrevRank ; Rank = Pos ),
    put_dict(rank, E, Rank, R),
    Pos1 is Pos + 1,
    number_ranks(T, Basis, Pos1, P, Rank, Rs).

% ===================================================================
% 4. GAME TABLE (in memory, keyed by generated id)
% ===================================================================
new_id(Id) :-
    random_between(0, 0xFFFFFFFFFF, A), random_between(0, 0xFFFFFFFFFF, B),
    format(atom(Id), 'g~16r~16r', [A, B]).

save_game(S0) :-
    get_time(Now), put_dict(touched, S0, Now, S),
    get_dict(id, S, Id),
    retractall(game_rec(Id, _)), assertz(game_rec(Id, S)).

gc_games :-
    get_time(Now),
    forall(( game_rec(Id, S), get_dict(touched, S, T), Now - T > 43200 ),
           retractall(game_rec(Id, _))).

api_error(Status, Code, Extra) :- throw(api_error(Status, Code, Extra)).

load_game(Body, S) :-
    (   is_dict(Body), get_dict(game, Body, Id0), catch(atom_string(Id, Id0), _, fail)
    ->  true
    ;   api_error(400, missing_game, _{message:"Field 'game' is required."})
    ),
    (   game_rec(Id, S) -> true
    ;   api_error(404, game_not_found, _{message:"Unknown game id."})
    ).

require_single(S) :-
    get_dict(multi, S, M),
    (   M == true -> api_error(403, not_allowed_in_multiplayer, none) ; true ).

require_status(S, Allowed) :-
    get_dict(status, S, St),
    (   memberchk(St, Allowed) -> true
    ;   api_error(409, wrong_status, _{message:"Not allowed in this state.", status:St})
    ).

% ---- JSON view of a game ------------------------------------------------
state_json(S, J) :-
    get_time(Now),
    elapsed_ms(S, Now, El),
    get_dict(pegs, S, Pegs), pegs_out(Pegs, PegsOut),
    get_dict(moves, S, Moves), get_dict(limit, S, Limit),
    get_dict(players, S, Players), get_dict(current, S, Cur),
    nth0(Cur, Players, CurName),
    get_dict(status, S, St), get_dict(history, S, Hist), get_dict(multi, S, Multi),
    (   Moves > Limit -> Over = true ; Over = false ),
    (   Multi == false, Hist \== [] -> CanUndo = true ; CanUndo = false ),
    (   St == playing -> Running = true ; Running = false ),
    get_dict(id, S, Id), get_dict(mode, S, Mode), get_dict(mode_random, S, MR),
    get_dict(n, S, N), get_dict(par, S, Par), get_dict(basis, S, Basis),
    get_dict(basis_random, S, BR), get_dict(results, S, Results),
    J = _{ game:Id, mode:Mode, mode_random:MR, discs:N, par:Par, limit:Limit,
           basis:Basis, basis_random:BR, multi:Multi, players:Players,
           current:Cur, current_name:CurName, status:St, pegs:PegsOut,
           moves:Moves, over_limit:Over, can_undo:CanUndo, elapsed_ms:El,
           running:Running, results:Results }.

pegs_out(Pegs, Out) :- maplist(reverse, Pegs, Out).

% ---- body helpers -------------------------------------------------------
read_body(Request, Body) :-
    catch(http_read_json_dict(Request, Body), _, api_error(400, bad_json, _{message:"Body must be valid JSON."})),
    (   is_dict(Body) -> true ; api_error(400, bad_json, _{message:"Body must be a JSON object."}) ).

body_peg(Body, Key, V) :-
    (   get_dict(Key, Body, V), integer(V), between(0, 2, V) -> true
    ;   api_error(400, bad_tower, _{message:"'from' and 'to' must be integers 0..2.", field:Key})
    ).

text_arg(V, Text) :- ( string(V) ; atom(V) ), !, atom_string(V, Text).

clean_name(V, Name) :-
    text_arg(V, S0),
    split_string(S0, "", " \t\r\n", [Name]),
    string_length(Name, L), L >= 1, L =< 24.

% ===================================================================
% 5. LEADERBOARD  (persisted to leaderboard.json)
% ===================================================================
lb_file(F) :- base_dir(D), atomic_list_concat([D, '/leaderboard.json'], F).

bases([moves, time]).

lb_load :-
    retractall(lb_entries(_, _, _)),
    lb_file(F),
    (   exists_file(F),
        catch(setup_call_cleanup(open(F, read, In, [encoding(utf8)]),
                                 json_read_dict(In, D), close(In)), _, fail),
        is_dict(D)
    ->  true ; D = _{} ),
    forall(( mode_def(M, _, _), bases(Bs), member(B, Bs) ),
           (   get_dict(M, D, MD), is_dict(MD), get_dict(B, MD, L), is_list(L)
           ->  assertz(lb_entries(M, B, L))
           ;   assertz(lb_entries(M, B, []))
           )).

lb_save :-
    lb_file(F),
    findall(M-MD, ( mode_def(M, _, _),
                    findall(B-L, ( bases(Bs), member(B, Bs), lb_entries(M, B, L) ), BP),
                    dict_pairs(MD, _, BP) ), MP),
    dict_pairs(All, _, MP),
    catch(setup_call_cleanup(open(F, write, Out, [encoding(utf8)]),
                             json_write_dict(Out, All, [width(0)]), close(Out)),
          E, print_message(warning, E)).

lb_submit(Mode, Basis, Entry) :-
    ( lb_entries(Mode, Basis, Old) -> true ; Old = [] ),
    sort_entries(Basis, [Entry|Old], Sorted),
    length(Top, 10), ( append(Top, _, Sorted) -> New = Top ; New = Sorted ),
    retractall(lb_entries(Mode, Basis, _)),
    assertz(lb_entries(Mode, Basis, New)),
    lb_save.

lb_json(Mode, Basis, _{mode:Mode, basis:Basis, entries:Ranked}) :-
    ( lb_entries(Mode, Basis, L) -> true ; L = [] ),
    sort_entries(Basis, L, Sorted),
    rank_sorted(Basis, Sorted, Ranked).

% ===================================================================
% 6. ENDPOINTS
% ===================================================================
:- http_handler(root(.),                index_page,    []).
:- http_handler(root(api/modes),        api_modes,     [method(get)]).
:- http_handler(root(api/'random-mode'),  api_random_mode,  [method(get)]).
:- http_handler(root(api/'random-basis'), api_random_basis, [method(get)]).
:- http_handler(root(api/new),          api_new,       [method(post)]).
:- http_handler(root(api/begin),        api_begin,     [method(post)]).
:- http_handler(root(api/move),         api_move,      [method(post)]).
:- http_handler(root(api/undo),         api_undo,      [method(post)]).
:- http_handler(root(api/restart),      api_restart,   [method(post)]).
:- http_handler(root(api/pause),        api_pause,     [method(post)]).
:- http_handler(root(api/finish),       api_finish,    [method(post)]).
:- http_handler(root(api/state),        api_state,     [method(get)]).
:- http_handler(root(api/leaderboard),  api_leaderboard, [method(get)]).

%   guarded(:Goal) -- run Goal, turn api_error/3 and unexpected errors into JSON.
guarded(Goal) :-
    catch(Goal, Err, error_reply(Err)).

error_reply(api_error(Status, Code, Extra)) :- !,
    (   is_dict(Extra) -> put_dict(error, Extra, Code, D) ; D = _{error:Code} ),
    reply_json_dict(D, [status(Status)]).
error_reply(E) :-
    print_message(error, E),
    reply_json_dict(_{error:server_error}, [status(500)]).

locked(Goal) :- with_mutex(hanoi_games, Goal).

api_modes(_Request) :-
    guarded(( findall(_{id:M, discs:N, par:P, factor:F, limit:L},
                      ( mode_def(M, N, F), mode_numbers(M, N, P, L) ), Ms),
              reply_json_dict(_{modes:Ms}) )).

api_random_mode(_Request) :-
    guarded(( findall(M, mode_def(M, _, _), Ms), random_member(Pick, Ms),
              reply_json_dict(_{mode:Pick}) )).

api_random_basis(_Request) :-
    guarded(( bases(Bs), random_member(Pick, Bs),
              reply_json_dict(_{basis:Pick}) )).

% ---- POST /api/new -----------------------------------------------------
api_new(Request) :-
    guarded(( read_body(Request, Body), locked(do_new(Body, Reply)), reply_json_dict(Reply) )).

do_new(Body, _{ok:true, state:J}) :-
    % players
    (   get_dict(players, Body, Ps0), is_list(Ps0), length(Ps0, Len), between(1, 4, Len),
        maplist(clean_name, Ps0, Players)
    ->  true
    ;   api_error(400, bad_players, _{message:"Provide 1 to 4 players, each with a name of 1-24 characters."})
    ),
    % mode (random is resolved here, by Prolog)
    (   get_dict(mode, Body, M0), text_arg(M0, MS), atom_string(MA, MS) -> true
    ;   api_error(400, bad_mode, _{message:"Field 'mode' is required."})
    ),
    (   MA == random
    ->  findall(M, mode_def(M, _, _), Ms), random_member(Mode, Ms), ModeRandom = true
    ;   mode_def(MA, _, _) -> Mode = MA, ModeRandom = false
    ;   api_error(400, bad_mode, _{message:"Unknown mode."})
    ),
    % basis
    (   get_dict(basis, Body, B0), text_arg(B0, BS), atom_string(BA, BS) -> true
    ;   api_error(400, bad_basis, _{message:"Field 'basis' is required."})
    ),
    (   get_dict(basis_random, Body, BRflag), BRflag == true -> BR0 = true ; BR0 = false ),
    (   BA == random
    ->  bases(Bs), random_member(Basis, Bs), BasisRandom = true
    ;   memberchk(BA, [moves, time]) -> Basis = BA, BasisRandom = BR0
    ;   api_error(400, bad_basis, _{message:"basis must be moves, time or random."})
    ),
    mode_numbers(Mode, N, Par, Limit),
    initial_pegs(N, Pegs),
    ( Len > 1 -> Multi = true ; Multi = false ),
    new_id(Id),
    gc_games,
    S = _{ id:Id, mode:Mode, mode_random:ModeRandom, n:N, par:Par, limit:Limit,
           basis:Basis, basis_random:BasisRandom, multi:Multi, players:Players,
           current:0, pegs:Pegs, moves:0, history:[], acc_ms:0, run_since:none,
           status:ready, results:[], touched:0 },
    save_game(S),
    game_rec(Id, S1),
    state_json(S1, J).

% ---- POST /api/begin ---------------------------------------------------
api_begin(Request) :-
    guarded(( read_body(Request, Body), locked(do_begin(Body, Reply)), reply_json_dict(Reply) )).

do_begin(Body, _{ok:true, state:J}) :-
    load_game(Body, S0),
    require_status(S0, [ready, playing]),
    (   get_dict(status, S0, ready)
    ->  get_time(Now),
        put_dict(_{status:playing, run_since:Now}, S0, S1),
        save_game(S1)
    ;   S1 = S0
    ),
    state_json(S1, J).

% ---- POST /api/move ----------------------------------------------------
api_move(Request) :-
    guarded(( read_body(Request, Body), locked(do_move(Body, Reply)), reply_json_dict(Reply) )).

do_move(Body, Reply) :-
    load_game(Body, S0),
    require_status(S0, [playing]),
    body_peg(Body, from, From), body_peg(Body, to, To),
    get_dict(pegs, S0, Pegs0),
    (   check_move(Pegs0, From, To, Pegs, Reason), var(Reason) -> true
    ;   api_error(422, invalid_move, _{reason:Reason, message:"That move is not allowed."})
    ),
    get_dict(moves, S0, M0), M is M0 + 1,
    get_dict(history, S0, H0),
    put_dict(_{pegs:Pegs, moves:M, history:[h(Pegs0, M0, From, To)|H0]}, S0, S1),
    get_dict(n, S1, N),
    pegs_out(Pegs, PegsOut),
    (   solved(N, Pegs)
    ->  finish_player(S1, Result, S2),
        get_dict(status, S2, St),
        ( St == finished -> GameOver = true ; GameOver = false ),
        save_game(S2),
        state_json(S2, J),
        Reply = _{ok:true, finished:true, game_over:GameOver, result:Result,
                  moves:M, pegs:PegsOut, state:J }
    ;   save_game(S1),
        state_json(S1, J),
        Reply = _{ok:true, finished:false, game_over:false,
                  moves:M, pegs:PegsOut, state:J }
    ).

%   finish_player(+S, -Result, -S2): record result + leaderboard, advance turn.
finish_player(S, Result, S2) :-
    get_time(Now),
    elapsed_ms(S, Now, Ms), TimeS is Ms // 1000,
    get_dict(moves, S, Moves), get_dict(par, S, Par), get_dict(limit, S, Limit),
    stars(Moves, Par, Limit, Stars),
    ( Moves > Limit -> Over = true ; Over = false ),
    get_dict(players, S, Players), get_dict(current, S, Cur), nth0(Cur, Players, Name),
    get_dict(id, S, Id), format(atom(EntryId), '~w-~w', [Id, Cur]),
    format_time(atom(Date), '%Y-%m-%d', Now),
    Result = _{ id:EntryId, player:Name, index:Cur, moves:Moves, time_ms:Ms,
                time_s:TimeS, stars:Stars, over:Over, date:Date },
    get_dict(mode, S, Mode), get_dict(basis, S, Basis),
    lb_submit(Mode, Basis, Result),
    get_dict(results, S, R0), append(R0, [Result], R1),
    get_dict(n, S, N), length(Players, Len),
    (   Cur + 1 < Len
    ->  Next is Cur + 1, initial_pegs(N, P0),
        put_dict(_{results:R1, current:Next, pegs:P0, moves:0, history:[],
                   acc_ms:0, run_since:none, status:ready}, S, S2)
    ;   put_dict(_{results:R1, acc_ms:Ms, run_since:none, status:finished}, S, S2)
    ).

% ---- POST /api/undo, /api/restart, /api/pause (single player only) -----
api_undo(Request) :-
    guarded(( read_body(Request, Body), locked(do_undo(Body, Reply)), reply_json_dict(Reply) )).

do_undo(Body, _{ok:true, undone:_{from:From, to:To}, state:J}) :-
    load_game(Body, S0),
    require_single(S0),
    require_status(S0, [playing]),
    get_dict(history, S0, H0),
    (   H0 = [h(Pegs, Moves, From, To)|H] -> true
    ;   api_error(409, nothing_to_undo, _{message:"There is no move to undo."})
    ),
    put_dict(_{pegs:Pegs, moves:Moves, history:H}, S0, S1),   % undo restores the counter too
    save_game(S1),
    state_json(S1, J).

api_restart(Request) :-
    guarded(( read_body(Request, Body), locked(do_restart(Body, Reply)), reply_json_dict(Reply) )).

do_restart(Body, _{ok:true, state:J}) :-
    load_game(Body, S0),
    require_single(S0),
    require_status(S0, [playing, paused]),
    get_dict(n, S0, N), initial_pegs(N, P0), get_time(Now),
    put_dict(_{pegs:P0, moves:0, history:[], acc_ms:0, run_since:Now, status:playing}, S0, S1),
    save_game(S1),
    state_json(S1, J).

api_pause(Request) :-
    guarded(( read_body(Request, Body), locked(do_pause(Body, Reply)), reply_json_dict(Reply) )).

do_pause(Body, _{ok:true, state:J}) :-
    load_game(Body, S0),
    require_single(S0),
    require_status(S0, [playing, paused]),
    (   get_dict(paused, Body, P), memberchk(P, [true, false]) -> true
    ;   api_error(400, bad_paused, _{message:"'paused' must be true or false."})
    ),
    get_time(Now), get_dict(status, S0, St),
    (   P == true, St == playing
    ->  elapsed_ms(S0, Now, Ms),
        put_dict(_{acc_ms:Ms, run_since:none, status:paused}, S0, S1)
    ;   P == false, St == paused
    ->  put_dict(_{run_since:Now, status:playing}, S0, S1)
    ;   S1 = S0
    ),
    save_game(S1),
    state_json(S1, J).

% ---- POST /api/finish, GET /api/state, GET /api/leaderboard ------------
api_finish(Request) :-
    guarded(( read_body(Request, Body), locked(do_finish(Body, Reply)), reply_json_dict(Reply) )).

do_finish(Body, Reply) :-
    load_game(Body, S),
    require_status(S, [finished]),
    get_dict(results, S, Rs), get_dict(basis, S, Basis), get_dict(mode, S, Mode),
    sort_entries(Basis, Rs, Sorted), rank_sorted(Basis, Sorted, Ranked),
    lb_json(Mode, Basis, LB),
    state_json(S, J),
    Reply = _{ok:true, ranking:Ranked, leaderboard:LB, state:J }.

api_state(Request) :-
    guarded(( http_parameters(Request, [game(G, [atom])]),
              locked(( load_game(_{game:G}, S), state_json(S, J) )),
              reply_json_dict(_{ok:true, state:J}) )).

api_leaderboard(Request) :-
    guarded(( http_parameters(Request, [mode(M, [optional(true)]), basis(B, [optional(true)])]),
              locked(do_leaderboard(M, B, Reply)),
              reply_json_dict(Reply) )).

do_leaderboard(M, B, Reply) :-
    (   var(M), var(B)
    ->  findall(LB, ( mode_def(Mo, _, _), bases(Bs), member(Ba, Bs), lb_json(Mo, Ba, LB) ), L),
        Reply = _{ok:true, leaderboards:L}
    ;   nonvar(M), nonvar(B), mode_def(M, _, _), memberchk(B, [moves, time])
    ->  lb_json(M, B, LB), Reply = _{ok:true, leaderboard:LB}
    ;   api_error(400, bad_query, _{message:"Give both mode and basis, or neither."})
    ).

% ===================================================================
% 7. PAGE  (HTML + CSS + JS embedded as raw strings)
% ===================================================================
index_page(_Request) :-
    page_html(Html),
    format('Content-Type: text/html; charset=UTF-8~n'),
    format('Cache-Control: no-store~n~n'),
    write(Html).

page_html(Html) :-
    css_source(Css), body_source(Body), js_source(Js),
    atomic_list_concat([ '<!DOCTYPE html>\n<html lang="en"><head><meta charset="utf-8">\n',
                         '<meta name="viewport" content="width=device-width,initial-scale=1">\n',
                         '<title>Tower of Hanoi</title>\n<style>\n', Css, '\n</style></head>\n<body>\n',
                         Body, '\n<script>\n', Js, '\n</script>\n</body></html>\n' ], Html).

% ===================================================================
% 8. SERVER START  (initialization/1: runs after load, never halts,
%    stops an older instance first so re-consulting works)
% ===================================================================
start_hanoi :-
    server_port(Port),
    stop_hanoi,
    lb_load,
    (   catch(http_server(http_dispatch, [port(Port)]), E,
              ( print_message(error, E), fail ))
    ->  format('~nTower of Hanoi is running at http://localhost:~w/~n(stop with ?- stop_hanoi. or ?- halt.)~n', [Port]),
        format(atom(Url), 'http://localhost:~w/', [Port]),
        catch(www_open_url(Url), _, true)
    ;   format('Could not start the server (is port ~w already in use?)~n', [Port])
    ).

stop_hanoi :-
    server_port(Port),
    catch(http_stop_server(Port, []), _, true).

:- initialization(start_hanoi).

% ===================================================================
% 9. EMBEDDED FRONT-END
% ===================================================================

% ---------------- CSS ----------------
css_source({|raw||
:root{
  --p-50:#eef5f3;--p-100:#d9e8e4;--p-200:#b9d4cd;--p-300:#98bfb5;--p-400:#77A39A;
  --p-500:#5c8a80;--p-600:#477068;--p-700:#35564f;--p-800:#263f3a;--p-900:#172825;
  --ink:#17302c;--serif:"Hiragino Mincho ProN","Yu Mincho","Noto Serif JP",Georgia,serif;
  --sans:"Segoe UI",system-ui,-apple-system,Roboto,sans-serif;
}
*{box-sizing:border-box}
html,body{margin:0;height:100%;background:var(--p-800);color:var(--ink);font-family:var(--sans);overflow:hidden}
button{font:inherit;cursor:pointer}
.hidden,[hidden]{display:none!important}
.screen{display:none;position:fixed;inset:0}
.screen.active{display:flex}
:focus-visible{outline:3px solid #fff;outline-offset:2px;box-shadow:0 0 0 5px var(--p-800)}

/* ---------- shared widgets ---------- */
.center{align-items:center;justify-content:center;padding:16px;overflow:auto;
  background:radial-gradient(circle at 30% 20%,var(--p-500),var(--p-700) 60%,var(--p-900))}
.card{background:var(--p-50);border-radius:16px;padding:28px;width:min(560px,100%);
  box-shadow:0 14px 40px rgba(0,0,0,.35);border:2px solid var(--p-300);position:relative;z-index:1}
.card h1{font-family:var(--serif);font-size:1.9rem;margin:0 0 6px;color:var(--p-800)}
.card p.sub{margin:0 0 18px;color:var(--p-700)}
.btn{background:var(--p-700);color:#fff;border:2px solid var(--p-700);border-radius:10px;padding:.65em 1.2em;font-weight:600}
.btn:hover{background:var(--p-800)}
.btn.ghost{background:transparent;color:var(--p-700)}
.btn.ghost:hover{background:var(--p-100)}
.btn:disabled{opacity:.5;cursor:not-allowed}
.row{display:flex;gap:10px;flex-wrap:wrap;margin-top:18px}
.row.end{justify-content:flex-end}
.seg{display:flex;border:2px solid var(--p-700);border-radius:10px;overflow:hidden}
.seg button{flex:1;border:0;background:transparent;color:var(--p-800);padding:.6em;font-weight:600}
.seg button[aria-pressed=true]{background:var(--p-700);color:#fff}
.field{display:block;margin:12px 0 0;font-weight:600;color:var(--p-800)}
.field input{display:block;width:100%;margin-top:4px;padding:.6em .7em;border:2px solid var(--p-500);border-radius:8px;
  font:inherit;background:#fff;color:var(--ink)}
.field input[aria-invalid=true]{border-color:#a3261e;background:#fff4f2}
.err{color:#9a1f17;font-weight:600;min-height:1.4em;margin:10px 0 0}
.basis-grid{display:grid;gap:12px}
.basis-card{background:#fff;border:2px solid var(--p-500);border-radius:12px;padding:16px;text-align:left;color:var(--ink)}
.basis-card:hover{background:var(--p-100);border-color:var(--p-700)}
.basis-card b{display:block;font-family:var(--serif);font-size:1.2rem;color:var(--p-800)}
.basis-card small{color:var(--p-700)}
.basis-card.reveal{animation:flip 1.6s ease-in-out}
@keyframes flip{0%{transform:rotateX(0)}100%{transform:rotateX(1080deg)}}

/* ---------- screen 1 : mode select ---------- */
#screen-modes{flex-direction:column;background:var(--p-900)}
.panels{flex:1;display:flex;min-height:0}
.panel{position:relative;flex:1 1 0;min-width:0;min-height:0;overflow:hidden;cursor:pointer;
  background:linear-gradient(180deg,var(--b1),var(--b2));color:var(--fg);
  transition:flex-grow .55s cubic-bezier(.2,.7,.2,1);display:flex;flex-direction:column;align-items:center;justify-content:center}
.panels.has-focus .panel{flex-grow:.22}
.panels.has-focus .panel.focus{flex-grow:5}
.panel.theme-easy{--b1:#cfe3dc;--b2:#f2d3dc;--fg:#1d2b28}
.panel.theme-hard{--b1:#8a4b2d;--b2:#4a2f20;--fg:#fff3e4}
.panel.theme-difficult{--b1:#14233f;--b2:#0b1226;--fg:#e8f4ff}
.panel.theme-nightmare{--b1:#4a0d0d;--b2:#1a0505;--fg:#ffe8dc}
.panel.theme-random{--b1:#477068;--b2:#263f3a;--fg:#f2faf8}
.strip{display:flex;flex-direction:column;align-items:center;gap:14px;padding:12px;white-space:nowrap}
.strip svg{width:44px;height:44px}
.strip .ttl{font-family:var(--serif);font-size:1.5rem;font-weight:700}
.strip .hint{font-size:.85rem;opacity:.85}
.panels.has-focus .panel:not(.focus) .strip .ttl{writing-mode:vertical-rl}
.panels.has-focus .panel:not(.focus) .strip .hint{display:none}
.panels.has-focus .panel:not(.focus) .strip svg{width:30px;height:30px}
.panel.focus .strip{display:none}
.panel:not(.focus) .detail{display:none}
.panel+.panel{border-left:0}
.detail{width:100%;height:100%;min-width:300px;padding:22px 26px;display:flex;flex-direction:column;gap:10px;align-items:center}
.detail h2{margin:0;font-family:var(--serif);font-size:clamp(1.6rem,3vw,2.4rem);display:flex;align-items:center;gap:12px}
.detail h2 svg{width:36px;height:36px}
.detail .tag{margin:0;opacity:.9}
.chips{display:flex;gap:8px;flex-wrap:wrap;justify-content:center}
.chip{background:rgba(255,255,255,.16);border:1px solid rgba(255,255,255,.35);border-radius:999px;padding:.25em .8em;font-weight:600}
.theme-easy .chip{background:rgba(0,0,0,.08);border-color:rgba(0,0,0,.25)}
.demo{position:relative;flex:1;min-height:140px;width:min(100%,640px);border-radius:12px;overflow:hidden;border:2px solid rgba(255,255,255,.35)}
.snd{background:rgba(0,0,0,.35);color:inherit;border:2px solid currentColor;border-radius:999px;padding:.35em 1em;font-weight:600}
.theme-easy .snd{background:rgba(255,255,255,.55)}
.cta{font-weight:700;opacity:.95}
.qmark{font-family:var(--serif);font-size:clamp(5rem,16vw,11rem);line-height:1;animation:qfloat 3s ease-in-out infinite;text-shadow:0 0 30px rgba(255,255,255,.4)}
@keyframes qfloat{0%,100%{transform:translateY(0) rotate(-4deg)}50%{transform:translateY(-14px) rotate(4deg)}}
.lbbtn{position:fixed;right:12px;bottom:12px;z-index:5;background:var(--p-50);color:var(--p-800);border:2px solid var(--p-700);border-radius:999px;padding:.5em 1.1em;font-weight:700}
@media(max-width:767px){
  .panels{flex-direction:column}
  .panels.has-focus .panel{flex-grow:0;flex-basis:56px}
  .panels.has-focus .panel.focus{flex-grow:1}
  .panels.has-focus .panel:not(.focus) .strip{flex-direction:row}
  .panels.has-focus .panel:not(.focus) .strip .ttl{writing-mode:horizontal-tb;font-size:1.1rem}
  .panel{flex-basis:0}
  .detail{min-width:0;padding:12px}
  .strip .ttl{font-size:1.2rem}
}

/* ---------- play screen : left HUD rail + stage ---------- */
#screen-play{flex-direction:row;background:var(--p-900)}
.rail{width:268px;flex:none;background:var(--p-700);color:var(--p-50);padding:18px 16px;display:flex;flex-direction:column;gap:14px;
  overflow:auto;border-right:4px solid var(--p-400)}
.rail-mode{display:flex;gap:10px;align-items:center}
.rail-mode svg{width:36px;height:36px;flex:none}
.rail-mode b{font-family:var(--serif);font-size:1.4rem;display:block}
.rail-mode small{color:var(--p-100)}
.plist{list-style:none;margin:0;padding:0;display:flex;flex-direction:column;gap:6px}
.plist li{padding:6px 10px;border-radius:8px;background:var(--p-800);display:flex;justify-content:space-between;gap:8px;font-size:.95rem}
.plist li.cur{background:var(--p-50);color:var(--p-900);font-weight:700;outline:3px solid var(--p-400)}
.stats{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin:0}
.stats div{background:var(--p-800);border-radius:10px;padding:8px 10px}
.stats dt{font-size:.8rem;color:var(--p-200)}
.stats dd{margin:0;font-size:1.5rem;font-weight:700;font-variant-numeric:tabular-nums}
.badge{background:#ffd9d2;color:#7a1109;font-weight:800;border-radius:8px;padding:6px 10px;text-align:center;border:2px solid #b3261e;animation:pulse 1.2s infinite}
@keyframes pulse{50%{transform:scale(1.04)}}
.rail-actions{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:auto}
.rail-actions .btn{background:var(--p-100);color:var(--p-900);border-color:var(--p-100);padding:.55em .5em}
.rail-actions .btn:hover{background:#fff}
.rail-actions .btn:disabled{opacity:.45}
#stage{position:relative;flex:1;min-width:0;padding:14px}
.overlay{position:absolute;inset:0;z-index:20;background:rgba(23,40,37,.86);color:#fff;display:flex;flex-direction:column;
  align-items:center;justify-content:center;gap:16px;text-align:center;padding:20px}
.overlay h2{font-family:var(--serif);font-size:2.4rem;margin:0}
.overlay .btn{background:var(--p-100);color:var(--p-900);border-color:var(--p-100)}
@media(max-width:720px){
  #screen-play{flex-direction:column}
  .rail{width:100%;max-height:44vh;flex-direction:row;flex-wrap:wrap;gap:8px;border-right:0;border-bottom:4px solid var(--p-400);padding:10px}
  .rail-mode{flex:1 1 100%}
  .rail-mode small,.plist .done{display:none}
  .plist{flex-direction:row;flex-wrap:wrap}
  .stats{grid-template-columns:repeat(4,1fr);flex:1 1 100%}
  .stats dd{font-size:1.15rem}
  .rail-actions{grid-template-columns:repeat(5,auto);margin-top:0;flex:1 1 100%}
  #stage{padding:8px}
}

/* ---------- board / stage themes ---------- */
.board{position:relative;width:100%;height:100%;overflow:hidden;border-radius:14px;touch-action:none;user-select:none;
  background:linear-gradient(180deg,var(--sky1),var(--sky2));border:3px solid var(--p-400)}
.board.err{animation:shake .35s}
@keyframes shake{20%{transform:translateX(-9px)}40%{transform:translateX(9px)}60%{transform:translateX(-6px)}80%{transform:translateX(6px)}}
.scene,.amb,.fx-layer,.disc-layer{position:absolute;inset:0;pointer-events:none}
.scene svg{position:absolute;left:0;bottom:0;width:100%;height:100%}
.fx-layer{z-index:8;overflow:hidden}
.tower{position:absolute;top:0;bottom:0;width:33.3333%;pointer-events:none}
.rod{position:absolute;left:50%;bottom:7%;width:clamp(6px,4%,14px);height:80%;transform:translateX(-50%);border-radius:7px 7px 0 0;background:var(--rod)}
.plinth{position:absolute;left:5%;right:5%;bottom:0;height:7%;border-radius:8px;background:var(--plinth);transition:box-shadow .2s}
.tower.sel .plinth{box-shadow:0 0 0 3px #fff,0 0 18px 4px var(--glow)}
.tower.err .plinth{box-shadow:0 0 0 3px #ff5a4a}
.theme-easy{--sky1:#f9dfe6;--sky2:#d6ebe0;--rod:#a47b4f;--plinth:#7d5a37;--glow:#f7a8bd}
.theme-hard{--sky1:#f2b56b;--sky2:#7e3b25;--rod:#3a1a12;--plinth:#2a120c;--glow:#ffb347}
.theme-difficult{--sky1:#0a0d24;--sky2:#2a1250;--rod:#35e6ff;--plinth:#141b45;--glow:#ff3df0}
.theme-nightmare{--sky1:#1a0303;--sky2:#7a0f0a;--rod:#2a2228;--plinth:#120c10;--glow:#ff5a1f}
.theme-difficult .rod{box-shadow:0 0 12px #35e6ff,0 0 24px #35e6ff88}
.theme-nightmare .rod{box-shadow:0 0 10px #ff4a1a88}
.amb i{position:absolute;top:-6%;left:var(--x);width:var(--s);height:var(--s);animation:fall var(--d) linear var(--dl) infinite,sway calc(var(--d)/3) ease-in-out var(--dl) infinite alternate}
@keyframes fall{from{top:-6%}to{top:104%}}
@keyframes sway{from{margin-left:-18px}to{margin-left:18px}}
.amb.rise i{top:104%;animation-name:rise,sway}
@keyframes rise{from{top:104%}to{top:-6%}}
.theme-easy .amb i{background:#f6a9bd;border-radius:100% 0 100% 0;opacity:.85}
.theme-hard .amb i{background:#d9531e;border-radius:0 100% 0 100%;opacity:.9}
.theme-difficult .amb i{width:2px;height:calc(var(--s)*2.4);background:linear-gradient(#35e6ff,transparent);box-shadow:0 0 6px #35e6ff;opacity:.7}
.theme-nightmare .amb i{background:#ff6a1a;border-radius:50%;box-shadow:0 0 8px #ff4a1a;opacity:.9}
.lantern{position:absolute;top:0;width:clamp(16px,3vw,30px);height:clamp(22px,4vw,40px);background:radial-gradient(#ffd27a,#e8481f);
  border-radius:8px;box-shadow:0 0 18px #ff7a30;transform-origin:top center;animation:swing 3.4s ease-in-out infinite alternate}
@keyframes swing{from{transform:rotate(-7deg)}to{transform:rotate(7deg)}}
.flames{position:absolute;left:0;right:0;bottom:0;height:26%;display:flex;justify-content:space-around;align-items:flex-end}
.flames b{width:9%;height:100%;background:radial-gradient(ellipse at bottom,#ffb347,#ff4a1a 55%,transparent 72%);
  filter:blur(3px);opacity:.7;animation:flick 1.3s ease-in-out infinite alternate}
.flames b:nth-child(2n){animation-duration:1.7s;height:70%}.flames b:nth-child(3n){animation-duration:.9s;height:85%}
@keyframes flick{from{transform:scaleY(.8)}to{transform:scaleY(1.15)}}

.disc-layer{z-index:4}
.disc{position:absolute;left:0;top:0;border-radius:999px;will-change:transform;box-sizing:border-box;pointer-events:none}
.disc.dragging{z-index:9;filter:drop-shadow(0 8px 6px rgba(0,0,0,.45))}
.d-easy{background:repeating-linear-gradient(90deg,rgba(0,0,0,.06) 0 3px,transparent 3px 8px),
  linear-gradient(180deg,hsl(var(--h) 48% 66%),hsl(var(--h) 48% 44%));
  box-shadow:inset 0 2px 0 rgba(255,255,255,.4),inset 0 -3px 0 rgba(0,0,0,.25),0 2px 3px rgba(0,0,0,.35)}
.d-hard{background:linear-gradient(180deg,#c4342a,#6e0f0b);border:2px solid #e2bd52;
  box-shadow:inset 0 2px 0 rgba(255,255,255,.3),inset 0 0 0 1px #6b4a00,0 3px 4px rgba(0,0,0,.45)}
.d-difficult{background:rgba(8,12,34,.85);border:2px solid hsl(var(--h) 100% 66%);
  box-shadow:0 0 8px hsl(var(--h) 100% 60%),0 0 20px hsl(var(--h) 100% 55% / .6),inset 0 0 9px hsl(var(--h) 100% 60% / .7)}
.d-nightmare{background:linear-gradient(180deg,#322c39,#06050a);border:1px solid #4a3c4c;
  box-shadow:0 0 10px #ff4a1a99,0 0 24px #ff2a0055,inset 0 -3px 7px #ff4a1a66,inset 0 2px 2px rgba(255,255,255,.14)}
.d-nightmare::after{content:"";position:absolute;left:18%;right:22%;top:48%;height:2px;
  background:linear-gradient(90deg,transparent,#ff7a2a,transparent);opacity:.8}
.pt{position:absolute;pointer-events:none;will-change:transform,opacity}
.pt.petal{background:#f7a8bd;border-radius:100% 0 100% 0}
.pt.leaf{background:#d9531e;border-radius:0 100% 0 100%}
.pt.spark{border-radius:50%;background:#fff}
.pt.ember{background:#ff7a2a;border-radius:50%;box-shadow:0 0 8px #ff4a1a}
.pt.trail{border-radius:50%}

/* ---------- reveal / pass / results ---------- */
#reveal{position:fixed;inset:0;z-index:50;background:rgba(23,40,37,.94);color:#fff;display:flex;flex-direction:column;
  align-items:center;justify-content:center;gap:20px;perspective:900px}
.rcard{width:190px;height:250px;position:relative;transform-style:preserve-3d}
.rface{position:absolute;inset:0;backface-visibility:hidden;border-radius:16px;display:flex;flex-direction:column;
  align-items:center;justify-content:center;gap:10px;border:3px solid #fff;font-family:var(--serif);font-size:1.6rem}
.rface.front{background:var(--p-600);font-size:6rem}
.rface.back{transform:rotateY(180deg);background:linear-gradient(180deg,var(--b1),var(--b2));color:var(--fg)}
.rface.back svg{width:70px;height:70px}
.spin{animation:spin 2.2s cubic-bezier(.2,.7,.2,1) forwards}
@keyframes spin{from{transform:rotateY(0)}to{transform:rotateY(900deg)}}
.stars{font-size:3rem;letter-spacing:6px;color:#c98a00}
.stars .off{color:#b8c9c5}
.pass-name{font-family:var(--serif);font-size:clamp(2rem,6vw,3.4rem);color:var(--p-800);margin:8px 0}
.results{align-items:flex-start;overflow:auto}
.results .card{margin:auto;width:min(860px,100%)}
.metrics{display:flex;flex-wrap:wrap;gap:8px;margin:10px 0}
.metrics span{background:var(--p-100);border:1px solid var(--p-300);border-radius:8px;padding:.3em .7em;font-weight:600;color:var(--p-900)}
.flag{background:#ffd9d2!important;color:#7a1109!important;border-color:#b3261e!important}
table.rank{width:100%;border-collapse:collapse;margin:10px 0;font-variant-numeric:tabular-nums}
table.rank th,table.rank td{padding:7px 8px;text-align:left;border-bottom:1px solid var(--p-300)}
table.rank th{background:var(--p-200);color:var(--p-900)}
table.rank tr.me td{background:#fff3c4;font-weight:700}
.rank-wrap{overflow-x:auto}
h3.lbh{font-family:var(--serif);margin:18px 0 4px;color:var(--p-800)}
canvas#party{position:fixed;inset:0;width:100%;height:100%;z-index:0;pointer-events:none}
.modal{position:fixed;inset:0;z-index:60;background:rgba(23,40,37,.8);display:flex;align-items:center;justify-content:center;padding:14px}
.modal .card{max-height:92vh;overflow:auto}
.toast{position:absolute;left:50%;top:18px;transform:translateX(-50%);z-index:25;background:var(--p-50);color:var(--p-900);
  border:3px solid var(--p-600);border-radius:12px;padding:10px 18px;font-weight:700;box-shadow:0 8px 24px rgba(0,0,0,.4)}
@media(prefers-reduced-motion:reduce){.amb i,.lantern,.flames b,.qmark{animation:none}}
|}).

% ---------------- HTML ----------------
body_source({|raw||
<!-- Screen 1: mode select -->
<section id="screen-modes" class="screen active" aria-label="Choose a mode">
  <div class="panels" id="panels"></div>
  <button class="lbbtn" id="btn-lb" type="button">Leaderboards</button>
</section>

<!-- Screen 2: players -->
<section id="screen-players" class="screen center">
  <div class="card">
    <h1>Who is playing?</h1>
    <p class="sub" id="pl-mode"></p>
    <div class="seg" role="group" aria-label="Number of players type">
      <button type="button" id="seg-single" aria-pressed="true">Single Player</button>
      <button type="button" id="seg-multi" aria-pressed="false">Multiplayer</button>
    </div>
    <div class="seg" id="count-row" style="margin-top:10px" hidden role="group" aria-label="Player count"></div>
    <div id="names"></div>
    <p class="err" id="name-error" role="alert"></p>
    <div class="row end">
      <button class="btn ghost" type="button" id="pl-back">Back</button>
      <button class="btn" type="button" id="pl-next">Continue</button>
    </div>
  </div>
</section>

<!-- Screen 3: basis -->
<section id="screen-basis" class="screen center">
  <div class="card">
    <h1>How is the score judged?</h1>
    <p class="sub">The basis decides the ranking and the leaderboard you compete on.</p>
    <div class="basis-grid">
      <button class="basis-card" type="button" data-basis="moves"><b>Fewest Moves</b><small>The lowest move count wins.</small></button>
      <button class="basis-card" type="button" data-basis="time"><b>Fastest Time</b><small>The quickest finish wins (mm:ss).</small></button>
      <button class="basis-card" type="button" data-basis="random" id="basis-random"><b>Random</b><small>Let the game decide.</small></button>
    </div>
    <p class="err" id="basis-msg" style="color:var(--p-800)"></p>
    <div class="row"><button class="btn ghost" type="button" id="ba-back">Back</button></div>
  </div>
</section>

<!-- Screen 4: play (left HUD rail + stage) -->
<section id="screen-play" class="screen">
  <aside class="rail" aria-label="Game status">
    <div class="rail-mode"><span id="r-ico"></span><div><b id="r-mode"></b><small id="r-basis"></small></div></div>
    <ul class="plist" id="r-players"></ul>
    <dl class="stats">
      <div><dt>Moves</dt><dd id="r-moves">0</dd></div>
      <div><dt>Time</dt><dd id="r-time">00:00</dd></div>
      <div><dt>Par</dt><dd id="r-par">0</dd></div>
      <div><dt>Limit</dt><dd id="r-limit">0</dd></div>
    </dl>
    <div class="badge hidden" id="r-over">OVER LIMIT</div>
    <div class="rail-actions">
      <button class="btn" type="button" id="b-undo">Undo</button>
      <button class="btn" type="button" id="b-restart">Restart</button>
      <button class="btn" type="button" id="b-pause">Pause</button>
      <button class="btn" type="button" id="b-sound">Sound: on</button>
      <button class="btn" type="button" id="b-menu">Menu</button>
    </div>
  </aside>
  <main id="stage"></main>
</section>

<!-- Pass screen (multiplayer, between turns) -->
<section id="screen-pass" class="screen center">
  <div class="card" style="text-align:center">
    <h1>Pass to</h1>
    <div class="pass-name" id="pass-name"></div>
    <p class="sub" id="pass-info"></p>
    <div class="row" style="justify-content:center"><button class="btn" type="button" id="pass-go">I am ready, start my turn</button></div>
  </div>
</section>

<!-- Results -->
<section id="screen-results" class="screen center results">
  <canvas id="party"></canvas>
  <div class="card" id="res-card"></div>
</section>

<div id="reveal" class="hidden" aria-live="polite"></div>
<div id="modal" class="modal hidden"></div>
|}).

% ---------------- JavaScript ----------------
js_source({|raw||
'use strict';
/* =====================================================================
   FRONT-END.  Calls the Prolog endpoints, animates, plays synthesized
   audio.  It never decides whether a move of a real game is legal.
   Sections: A helpers/icons/scenes, B sound, C particles, D board,
             E demo, F screens and game controller, G celebration.
   ===================================================================== */

/* ---------------- A. helpers ---------------- */
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
function el(tag, props = {}, ...kids) {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(props)) {
    if (k === 'class') e.className = v;
    else if (k === 'text') e.textContent = v;
    else if (k === 'html') e.innerHTML = v;
    else if (k.startsWith('on')) e.addEventListener(k.slice(2), v);
    else e.setAttribute(k, v);
  }
  for (const kid of kids.flat()) if (kid != null) e.append(kid.nodeType ? kid : document.createTextNode(kid));
  return e;
}
const sleep = ms => new Promise(r => setTimeout(r, ms));
const rand = (a, b) => a + Math.random() * (b - a);
const fmtTime = ms => { const s = Math.floor(ms / 1000); return String(Math.floor(s / 60)).padStart(2, '0') + ':' + String(s % 60).padStart(2, '0'); };
const MODE_ORDER = ['easy', 'hard', 'difficult', 'nightmare'];
const BASIS_NAME = { moves: 'Fewest Moves', time: 'Fastest Time' };
const STAR_ON = '\u2605', STAR_OFF = '\u2606';
const starText = n => STAR_ON.repeat(n) + STAR_OFF.repeat(3 - n);

async function api(path, body) {
  const opt = body === undefined ? {} : { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body) };
  let res;
  try { res = await fetch(path, opt); } catch (e) { throw { status: 0, error: 'network' }; }
  let data = {};
  try { data = await res.json(); } catch (e) { /* empty body */ }
  if (!res.ok) throw Object.assign({ status: res.status }, data);
  return data;
}

const THEME = {
  easy:      { name: 'Easy',      tag: 'Spring sakura garden' },
  hard:      { name: 'Hard',      tag: 'Autumn temple at dusk' },
  difficult: { name: 'Difficult', tag: 'Neon Tokyo night' },
  nightmare: { name: 'Nightmare', tag: 'Oni realm of fire' },
  random:    { name: 'Random Mode', tag: 'Fate picks your tower' }
};
const ICON = {
  easy: '<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><g>' + [0, 72, 144, 216, 288].map(a => '<ellipse cx="12" cy="6.5" rx="3.3" ry="5" transform="rotate(' + a + ' 12 12)"/>').join('') + '</g><circle cx="12" cy="12" r="1.8" fill="#fff"/></svg>',
  hard: '<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M12 1l2.2 5.2 3.6-2-1 5.2 5.2-.6-3.4 3.8 3 2.4-5 1 .6 4.8-4.2-2.4L12 23v-6l-2.8 1.6L10 14 5 15l3-2.4L4.6 8.8l5.2.6-1-5.2 3.6 2z"/></svg>',
  difficult: '<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M13.5 1L4 14h6l-1.5 9L20 9h-6.5z"/></svg>',
  nightmare: '<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M3 1l6 6M21 1l-6 6"/><path d="M4 1l5 7-3 1zM20 1l-5 7 3 1z"/><circle cx="12" cy="14" r="8"/><path d="M8 11l3 2-3 1zM16 11l-3 2 3 1z" fill="#1a0505"/><path d="M8 19l1.4-3 1.2 2 1.4-2 1.4 2 1.2-2L16 19z" fill="#fff"/></svg>',
  random: '<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><text x="12" y="19" text-anchor="middle" font-size="20" font-weight="700" font-family="serif">?</text></svg>'
};

/* decorative scenes: inline SVG, no external files */
function sceneSVG(mode) {
  const open = '<svg viewBox="0 0 400 200" preserveAspectRatio="xMidYMax slice" aria-hidden="true">';
  const art = {
    easy: '<path d="M0 150 Q80 110 160 145 T330 135 T400 150 V200H0z" fill="#b9d9c5"/><path d="M0 175 Q100 150 200 170 T400 165 V200H0z" fill="#8fc2a0"/>' +
      '<path d="M40 200 Q48 140 36 100 M44 130 Q70 105 95 100" stroke="#6d4a33" stroke-width="7" fill="none" stroke-linecap="round"/>' +
      [[30, 90, 20], [60, 80, 24], [92, 96, 20], [48, 108, 18], [78, 112, 17], [20, 112, 14]].map(c => '<circle cx="' + c[0] + '" cy="' + c[1] + '" r="' + c[2] + '" fill="#f7b6c8" opacity=".9"/>').join('') +
      '<path d="M340 200 Q345 160 338 135" stroke="#6d4a33" stroke-width="5" fill="none"/><circle cx="336" cy="128" r="16" fill="#f7b6c8" opacity=".9"/><circle cx="352" cy="138" r="12" fill="#f4a3bb" opacity=".9"/>',
    hard: '<path d="M0 140 L60 80 L120 135 L190 70 L260 140 L330 90 L400 140 V200H0z" fill="#9b4b2c" opacity=".55"/>' +
      '<g fill="#3a1a12"><rect x="150" y="140" width="100" height="40"/><path d="M135 140 Q200 120 265 140 L255 128 Q200 108 145 128z"/><rect x="165" y="105" width="70" height="24"/><path d="M152 105 Q200 88 248 105 L238 95 Q200 80 162 95z"/><rect x="180" y="75" width="40" height="18"/><path d="M170 75 Q200 58 230 75 L222 66 Q200 52 178 66z"/><rect x="198" y="40" width="4" height="20"/></g>' +
      '<rect x="0" y="180" width="400" height="20" fill="#3a1a12"/><path d="M30 180 Q36 140 28 110" stroke="#2a120c" stroke-width="6" fill="none"/><circle cx="28" cy="104" r="20" fill="#d9531e"/><circle cx="46" cy="116" r="14" fill="#e8861f"/><circle cx="14" cy="118" r="13" fill="#b73a14"/>',
    difficult: '<g fill="#0e1233">' + [[0, 120, 36], [34, 90, 30], [62, 130, 34], [98, 70, 28], [140, 110, 40], [250, 95, 34], [282, 125, 30], [310, 80, 38], [350, 115, 50]].map(b => '<rect x="' + b[0] + '" y="' + b[1] + '" width="' + b[2] + '" height="' + (200 - b[1]) + '"/>').join('') + '</g>' +
      '<path d="M200 200 L188 120 L196 60 L200 40 L204 60 L212 120z" fill="none" stroke="#ff3d6e" stroke-width="2"/><path d="M190 110H210M193 90H207M196 70H204" stroke="#ff3d6e" stroke-width="2"/>' +
      [[10, 140], [22, 150], [44, 105], [70, 150], [76, 165], [150, 130], [165, 150], [262, 115], [292, 140], [322, 100], [368, 135], [380, 150]].map((w, i) => '<rect x="' + w[0] + '" y="' + w[1] + '" width="5" height="4" fill="' + (i % 2 ? '#35e6ff' : '#ff3df0') + '"/>').join('') +
      '<rect x="100" y="150" width="32" height="10" fill="#ff3df0" opacity=".8"/><rect x="330" y="160" width="26" height="9" fill="#35e6ff" opacity=".8"/>',
    nightmare: '<circle cx="300" cy="62" r="34" fill="#c4150c"/><circle cx="300" cy="62" r="46" fill="#c4150c" opacity=".25"/>' +
      '<path d="M0 150 L40 90 L70 130 L120 60 L170 130 L220 85 L270 140 L330 95 L400 150 V200H0z" fill="#1a0505"/>' +
      '<g fill="#0a0203"><path d="M150 200V120h10v-14l-10-22 18 12h28l18-12-10 22v14h10v80z"/><path d="M60 200V150h8v-20l-6-14 12 8 12-8-6 14v20h8v50z"/></g>' +
      '<path d="M0 190 Q50 170 100 188 T200 186 T300 188 T400 184 V200H0z" fill="#3a0806"/>'
  };
  return open + (art[mode] || '') + '</svg>';
}

/* ---------------- B. sound (Web Audio, synthesized) ---------------- */
const Sound = (() => {
  let ctx = null, master = null, noiseBuf = null, enabled = true, amb = null;
  const YO = [293.66, 329.63, 392.0, 440.0, 493.88, 587.33, 659.25, 783.99, 880.0];
  function unlock() {
    try {
      if (!ctx) {
        const AC = window.AudioContext || window.webkitAudioContext;
        if (!AC) return false;
        ctx = new AC(); master = ctx.createGain(); master.gain.value = 0.55; master.connect(ctx.destination);
        noiseBuf = ctx.createBuffer(1, ctx.sampleRate, ctx.sampleRate);
        const d = noiseBuf.getChannelData(0);
        for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;
      }
      if (ctx.state === 'suspended') ctx.resume();
      return true;
    } catch (e) { return false; }
  }
  const ok = () => enabled && ctx;
  function tone(o) {
    const t0 = ctx.currentTime + (o.t || 0), a = o.a == null ? 0.005 : o.a, d = o.d == null ? 0.3 : o.d;
    const osc = ctx.createOscillator(), g = ctx.createGain();
    osc.type = o.type || 'sine';
    osc.frequency.setValueAtTime(o.f, t0);
    if (o.to) osc.frequency.exponentialRampToValueAtTime(o.to, t0 + d);
    g.gain.setValueAtTime(0.0001, t0);
    g.gain.exponentialRampToValueAtTime(o.v == null ? 0.2 : o.v, t0 + a);
    g.gain.exponentialRampToValueAtTime(0.0001, t0 + d);
    let n = osc;
    if (o.lp) {
      const f = ctx.createBiquadFilter(); f.type = 'lowpass'; f.frequency.setValueAtTime(o.lp, t0);
      if (o.lpTo) f.frequency.exponentialRampToValueAtTime(o.lpTo, t0 + d);
      osc.connect(f); n = f;
    }
    n.connect(g); g.connect(master); osc.start(t0); osc.stop(t0 + d + 0.05);
  }
  function noise(o) {
    const t0 = ctx.currentTime + (o.t || 0), d = o.d || 0.2;
    const src = ctx.createBufferSource(); src.buffer = noiseBuf; src.loop = true;
    const f = ctx.createBiquadFilter(); f.type = o.type || 'lowpass'; f.frequency.value = o.f || 1000;
    const g = ctx.createGain();
    g.gain.setValueAtTime(0.0001, t0); g.gain.exponentialRampToValueAtTime(o.v || 0.1, t0 + 0.01); g.gain.exponentialRampToValueAtTime(0.0001, t0 + d);
    src.connect(f); f.connect(g); g.connect(master); src.start(t0); src.stop(t0 + d + 0.05);
  }
  const note = r => YO[Math.max(0, Math.min(4, Math.round(r * 4)))];
  const pluck = (f, t, v) => { tone({ f, t, d: 0.9, type: 'triangle', v, a: 0.004 }); tone({ f: f * 2, t, d: 0.4, v: v / 3, a: 0.004 }); };
  const drum = (t, f0, f1, v) => { tone({ f: f0, to: f1, t, d: 0.4, v }); noise({ t, d: 0.12, v: v / 3, f: 500 }); };
  const voices = {
    easy: {
      lift: r => pluck(note(r) * 1.5, 0, 0.2),
      land: r => { pluck(note(r) / 2, 0, 0.3); pluck(note(Math.min(1, r + 0.5)), 0.07, 0.22); noise({ d: 0.25, v: 0.03, type: 'highpass', f: 6000 }); }
    },
    hard: {
      lift: () => drum(0, 150, 90, 0.25),
      land: () => { drum(0, 160, 48, 0.6); noise({ d: 0.2, v: 0.05, type: 'highpass', f: 3000 }); }
    },
    difficult: {
      lift: r => tone({ f: 200 * (1 + r), to: 520 * (1 + r), d: 0.28, type: 'sawtooth', v: 0.12, lp: 900, lpTo: 3500 }),
      land: r => { tone({ f: 110 * (1 + r), d: 0.3, type: 'sawtooth', v: 0.14, lp: 1800 }); tone({ f: 111 * (1 + r), d: 0.3, type: 'sawtooth', v: 0.1, lp: 1800 }); tone({ f: 1760, d: 0.16, v: 0.07, t: 0.04 }); }
    },
    nightmare: {
      lift: () => { tone({ f: 70, to: 95, d: 0.45, type: 'sawtooth', v: 0.2, lp: 300, lpTo: 700 }); noise({ d: 0.4, v: 0.06, f: 600 }); },
      land: () => { tone({ f: 90, to: 35, d: 0.65, v: 0.6 }); noise({ d: 0.25, v: 0.14, f: 900 }); for (let i = 0; i < 3; i++) noise({ t: 0.05 + i * 0.07 + Math.random() * 0.05, d: 0.04, v: 0.1, type: 'highpass', f: 2500 }); }
    }
  };
  function play(kind, mode, r) {
    if (!ok()) return;
    r = r == null ? 0.5 : r;
    try {
      if (kind === 'error') { tone({ f: 170, to: 90, d: 0.2, type: 'square', v: 0.12, lp: 900 }); return; }
      if (kind === 'reveal') { [0, 1, 2, 3, 4].forEach(i => tone({ f: YO[i + 2] * 1.5, t: i * 0.09, d: 0.5, type: 'triangle', v: 0.12 })); return; }
      if (kind === 'fanfare') { [523.25, 659.25, 783.99, 1046.5, 1318.5].forEach((f, i) => { tone({ f, t: i * 0.14, d: 0.9, type: 'sawtooth', v: 0.1, lp: 3000 }); tone({ f: f / 2, t: i * 0.14, d: 0.9, type: 'square', v: 0.05, lp: 1500 }); }); return; }
      const v = voices[mode] || voices.easy;
      if (v[kind]) v[kind](r);
    } catch (e) { /* audio is optional */ }
  }
  function stopAmbient() { if (amb) { amb.stop(); amb = null; } }
  function ambient(mode) {
    stopAmbient();
    if (!ok()) return;
    if (mode === 'nightmare') {
      const o1 = ctx.createOscillator(), o2 = ctx.createOscillator(), f = ctx.createBiquadFilter(), g = ctx.createGain(), lfo = ctx.createOscillator(), lg = ctx.createGain();
      o1.type = o2.type = 'sawtooth'; o1.frequency.value = 55; o2.frequency.value = 55.7; f.type = 'lowpass'; f.frequency.value = 170;
      lfo.frequency.value = 0.12; lg.gain.value = 60; lfo.connect(lg); lg.connect(f.frequency);
      g.gain.setValueAtTime(0.0001, ctx.currentTime); g.gain.exponentialRampToValueAtTime(0.05, ctx.currentTime + 2.5);
      o1.connect(f); o2.connect(f); f.connect(g); g.connect(master); o1.start(); o2.start(); lfo.start();
      amb = { stop() { try { g.gain.exponentialRampToValueAtTime(0.0001, ctx.currentTime + 0.4); [o1, o2, lfo].forEach(o => o.stop(ctx.currentTime + 0.5)); } catch (e) { /* ignore */ } } };
      return;
    }
    const step = { easy: 3200, hard: 2600, difficult: 520 }[mode] || 3000;
    let i = 0;
    const iv = setInterval(() => {
      if (!ok()) return;
      i++;
      if (mode === 'easy') pluck(YO[Math.floor(Math.random() * 6)] / 2, 0, 0.07);
      else if (mode === 'hard') drum(0, 110, 60, i % 4 === 0 ? 0.22 : 0.1);
      else tone({ f: [110, 130.8, 164.8, 196, 164.8, 130.8][i % 6] * 2, d: 0.4, type: 'sawtooth', v: 0.04, lp: 1400 });
    }, step);
    amb = { stop() { clearInterval(iv); } };
  }
  return { unlock, play, ambient, stopAmbient, setEnabled(b) { enabled = b; if (!b) stopAmbient(); }, isEnabled: () => enabled };
})();

/* ---------------- C. particles ---------------- */
const FX = {
  active: 0,
  spawn(layer, cls, x, y, size, frames, dur, css) {
    if (this.active > 140) return;
    const p = el('i', { class: 'pt ' + cls });
    p.style.cssText = 'left:' + (x - size / 2) + 'px;top:' + (y - size / 2) + 'px;width:' + size + 'px;height:' + size + 'px;' + (css || '');
    layer.append(p); this.active++;
    const a = p.animate(frames, { duration: dur, easing: 'ease-out', fill: 'forwards' });
    const done = () => { if (p.isConnected) { p.remove(); this.active--; } };
    a.onfinish = done; a.oncancel = done;
  },
  burst(layer, x, y, mode) {
    const T = (dx, dy, r, s) => 'translate(' + dx + 'px,' + dy + 'px) rotate(' + r + 'deg) scale(' + (s == null ? 1 : s) + ')';
    if (mode === 'easy') {
      for (let i = 0; i < 12; i++) {
        const dx = rand(-70, 70), dy = rand(-60, -10), r = rand(-300, 300);
        this.spawn(layer, 'petal', x, y, rand(8, 14), [{ transform: T(0, 0, 0), opacity: 1 }, { transform: T(dx, dy, r / 2), opacity: 1, offset: 0.4 }, { transform: T(dx * 1.3, dy + 100, r, 0.8), opacity: 0 }], rand(900, 1500));
      }
    } else if (mode === 'hard') {
      for (let i = 0; i < 9; i++) {
        const a0 = rand(0, 6.28), fr = [];
        for (let k = 0; k <= 10; k++) fr.push({ transform: T(Math.cos(a0 + k * 0.75) * k * 7, Math.sin(a0 + k * 0.75) * k * 3.5 - k * 5, k * 70), opacity: k > 7 ? 1 - (k - 7) / 3.5 : 1 });
        this.spawn(layer, 'leaf', x, y, rand(9, 15), fr, rand(900, 1400));
      }
    } else if (mode === 'difficult') {
      for (let i = 0; i < 14; i++) {
        const a = rand(0, 6.28), d = rand(30, 90), h = Math.random() < 0.5 ? 185 : 310;
        this.spawn(layer, 'spark', x, y, rand(3, 6), [{ transform: T(0, 0, 0), opacity: 1 }, { transform: T(Math.cos(a) * d, Math.sin(a) * d, 0, 0.3), opacity: 0 }], rand(450, 800), 'background:hsl(' + h + ' 100% 65%);box-shadow:0 0 8px hsl(' + h + ' 100% 60%)');
      }
    } else {
      for (let i = 0; i < 12; i++) {
        const dx = rand(-45, 45), dy = -rand(50, 130);
        this.spawn(layer, 'ember', x, y, rand(3, 7), [{ transform: T(0, 0, 0), opacity: 1 }, { transform: T(dx, dy, 0, 0.4), opacity: 0 }], rand(900, 1500));
      }
    }
  },
  trail(layer, x, y) {
    const h = 180 + Math.random() * 140;
    this.spawn(layer, 'trail', x, y, 12, [{ transform: 'scale(1)', opacity: 0.9 }, { transform: 'scale(.15)', opacity: 0 }], 520, 'background:hsl(' + h + ' 100% 62%);box-shadow:0 0 14px hsl(' + h + ' 100% 60%)');
  }
};

/* ambient decoration (falling petals / leaves / neon rain / embers) */
function ambientLayer(mode, count) {
  const wrap = el('div', { class: 'amb' + (mode === 'nightmare' ? ' rise' : '') });
  for (let i = 0; i < count; i++) {
    const s = rand(8, 15), d = rand(7, 14);
    const p = el('i');
    p.style.cssText = '--x:' + rand(0, 97) + '%;--s:' + (mode === 'difficult' ? rand(2, 3) : s) + 'px;--d:' + d + 's;--dl:-' + rand(0, d) + 's';
    wrap.append(p);
  }
  if (mode === 'difficult') for (let i = 0; i < 4; i++) { const l = el('div', { class: 'lantern' }); l.style.left = (10 + i * 25 + rand(-4, 4)) + '%'; l.style.animationDelay = '-' + rand(0, 3) + 's'; wrap.append(l); }
  if (mode === 'hard') for (let i = 0; i < 2; i++) { const l = el('div', { class: 'lantern' }); l.style.left = (i ? 84 : 12) + '%'; wrap.append(l); }
  if (mode === 'nightmare') wrap.append(el('div', { class: 'flames' }, ...[0, 1, 2, 3, 4, 5, 6].map(() => el('b'))));
  return wrap;
}

/* ---------------- D. board (pegs, discs, animation, pointer input) ----------------
   Pegs are arrays bottom-first, e.g. [[3,2,1],[],[]], exactly as sent by Prolog. */
const T = (x, y) => 'translate(' + x + 'px,' + y + 'px)';
const initPegs = n => [Array.from({ length: n }, (_, i) => n - i), [], []];

class Board {
  /* opts: interactive, onTry(from,to,o)->Promise, sfx(kind,ratio), ambCount */
  constructor(host, mode, n, opts = {}) {
    Object.assign(this, { host, mode, n, opts, pegs: [[], [], []], busy: false, locked: false, dead: false, selected: null, drag: null, anims: new Set(), timers: new Set(), W: 0, H: 0 });
    this.root = el('div', { class: 'board theme-' + mode });
    this.scene = el('div', { class: 'scene', html: sceneSVG(mode) });
    this.towers = [0, 1, 2].map(i => { const t = el('div', { class: 'tower' }); t.style.left = (i * 33.3333) + '%'; t.append(el('div', { class: 'rod' }), el('div', { class: 'plinth' })); return t; });
    this.layer = el('div', { class: 'disc-layer' });
    this.fx = el('div', { class: 'fx-layer' });
    this.root.append(this.scene, ambientLayer(mode, opts.ambCount || 12), ...this.towers, this.layer, this.fx);
    host.append(this.root);
    this.discEls = new Map();
    for (let d = 1; d <= n; d++) {
      const h = mode === 'difficult' ? 170 + (d - 1) * (170 / Math.max(1, n - 1)) : mode === 'easy' ? 22 + (d * 9) % 24 : 0;
      const e = el('div', { class: 'disc d-' + mode });
      e.style.setProperty('--h', h);
      this.discEls.set(d, e); this.layer.append(e);
    }
    this.ro = new ResizeObserver(() => { if (!this.animating) { this.layout(); this.place(); } });
    this.ro.observe(this.root);
    if (opts.interactive) this.bindPointer();
  }
  sfx(k, r) { if (this.opts.sfx) this.opts.sfx(k, r); }
  later(fn, ms) { const id = setTimeout(() => { this.timers.delete(id); fn(); }, ms); this.timers.add(id); }
  ratio(d) { return (d - 1) / Math.max(1, this.n - 1); }
  layout() {
    const r = this.root.getBoundingClientRect();
    this.W = r.width; this.H = r.height; this.tw = this.W / 3;
    this.baseH = this.H * 0.07;
    this.dh = Math.min(38, this.H * 0.78 / (this.n + 0.6));
    const wMax = this.tw * 0.92, wMin = Math.max(this.tw * 0.2, 22);
    this.discEls.forEach((e, d) => {
      const w = wMin + (wMax - wMin) * (d - 1) / Math.max(1, this.n - 1);
      e.style.width = w + 'px'; e.style.height = (this.dh - 2) + 'px'; e._w = w;
    });
  }
  pos(tower, level, w) { return { x: tower * this.tw + this.tw / 2 - w / 2, y: this.H - this.baseH - (level + 1) * this.dh + 1 }; }
  liftY() { return Math.max(2, this.H * 0.13 - this.dh * 1.4); }
  place() {
    if (!this.W) return;
    this.pegs.forEach((peg, i) => peg.forEach((d, lvl) => {
      const e = this.discEls.get(d), p = this.pos(i, lvl, e._w);
      e.style.transform = T(p.x, p.y);
    }));
  }
  setPegs(p) { this.pegs = p.map(a => a.slice()); this.deselect(true); this.layout(); this.place(); }
  top(i) { const p = this.pegs[i]; return p.length ? p[p.length - 1] : null; }

  run(elm, frames, dur) {
    return new Promise(res => {
      if (this.dead) return res(null);
      const a = elm.animate(frames, { duration: dur, fill: 'forwards' });
      this.anims.add(a);
      const done = () => { this.anims.delete(a); res(a); };
      a.onfinish = done; a.oncancel = done;
    });
  }
  /* animate the top disc of `from` to `to`; `after` is the new state from Prolog */
  async move(from, to, after, o = {}) {
    const d = this.top(from);
    if (d == null) { this.setPegs(after); return; }
    this.animating = true; this.busy = true;
    const e = this.discEls.get(d), w = e._w;
    const a = this.pos(from, this.pegs[from].length - 1, w), b = this.pos(to, this.pegs[to].length, w), ly = this.liftY();
    this.pegs = after.map(x => x.slice());
    e.style.transition = 'none'; e.style.zIndex = 6;
    let frames, dur = o.dur || 640;
    if (o.startPos) {
      const s = o.startPos;
      frames = [{ transform: T(s.x, s.y), easing: 'ease-out' }, { transform: T(b.x, Math.min(s.y, ly + this.dh)), easing: 'cubic-bezier(.5,0,1,.6)' }, { transform: T(b.x, b.y) }];
      frames[0].offset = 0; frames[1].offset = 0.5; frames[2].offset = 1; dur = o.dur || 420;
    } else if (o.lifted) {
      frames = [{ transform: T(a.x, ly), offset: 0, easing: 'ease-in-out' }, { transform: T(b.x, ly), offset: 0.6, easing: 'cubic-bezier(.5,0,1,.6)' }, { transform: T(b.x, b.y), offset: 1 }];
    } else {
      frames = [{ transform: T(a.x, a.y), offset: 0, easing: 'ease-out' }, { transform: T(a.x, ly), offset: 0.25, easing: 'ease-in-out' },
        { transform: T(b.x, ly), offset: 0.72, easing: 'cubic-bezier(.5,0,1,.6)' }, { transform: T(b.x, b.y), offset: 1 }];
      this.sfx('lift', this.ratio(d));
    }
    if (o.lifted || o.startPos) this.sfx('lift', this.ratio(d));
    let trail = null;
    if (this.mode === 'difficult') {
      trail = setInterval(() => {
        const r = e.getBoundingClientRect(), br = this.root.getBoundingClientRect();
        FX.trail(this.fx, r.left + r.width / 2 - br.left, r.top + r.height / 2 - br.top);
      }, 45);
    }
    const anim = await this.run(e, frames, dur);
    if (trail) clearInterval(trail);
    if (this.dead) return;
    e.style.transform = T(b.x, b.y); e.style.zIndex = '';
    if (anim) anim.cancel();
    this.sfx('land', this.ratio(d));
    FX.burst(this.fx, b.x + w / 2, b.y + this.dh / 2, this.mode);
    this.animating = false; this.busy = false;
  }
  shake(i) {
    this.root.classList.remove('err'); void this.root.offsetWidth; this.root.classList.add('err');
    if (i != null) { this.towers[i].classList.add('err'); this.later(() => this.towers[i].classList.remove('err'), 400); }
    this.later(() => this.root.classList.remove('err'), 400);
  }
  homeOf(i) { const d = this.top(i); if (d == null) return; const e = this.discEls.get(d), p = this.pos(i, this.pegs[i].length - 1, e._w); e.style.transition = 'transform .2s'; e.style.transform = T(p.x, p.y); e.classList.remove('dragging'); this.later(() => { e.style.transition = 'none'; }, 230); }
  reject(from, to) { this.sfx('error'); this.shake(to); this.homeOf(from); this.deselect(true); }

  /* ----- pointer input: drag and drop, or click source then target ----- */
  towerAt(x) { const r = this.root.getBoundingClientRect(); return Math.max(0, Math.min(2, Math.floor((x - r.left) / (r.width / 3)))); }
  select(i) {
    this.selected = i; this.towers[i].classList.add('sel');
    const d = this.top(i), e = this.discEls.get(d), p = this.pos(i, this.pegs[i].length - 1, e._w);
    e.style.transition = 'transform .15s'; e.style.transform = T(p.x, this.liftY());
  }
  deselect(quiet) {
    if (this.selected == null) return;
    const i = this.selected; this.selected = null; this.towers[i].classList.remove('sel');
    if (!quiet) this.homeOf(i);
  }
  tryMove(from, to, o) {
    this.busy = true;
    Promise.resolve(this.opts.onTry(from, to, o)).catch(() => {}).then(() => { this.busy = false; });
  }
  bindPointer() {
    const r = this.root;
    r.addEventListener('pointerdown', e => {
      if (this.busy || this.locked || (e.pointerType === 'mouse' && e.button !== 0)) return;
      Sound.unlock();
      const i = this.towerAt(e.clientX);
      if (this.selected != null) {
        const from = this.selected;
        if (from === i) { this.deselect(); return; }
        this.selected = null; this.towers[from].classList.remove('sel');
        this.tryMove(from, i, { lifted: true }); return;
      }
      if (this.top(i) == null) { this.sfx('error'); this.shake(i); return; }   // nothing to pick up here
      this.drag = { from: i, x0: e.clientX, y0: e.clientY, moved: false };
      try { r.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
    });
    r.addEventListener('pointermove', e => {
      const g = this.drag; if (!g) return;
      if (!g.moved && Math.hypot(e.clientX - g.x0, e.clientY - g.y0) > 7) {
        g.moved = true;
        const d = this.top(g.from); g.el = this.discEls.get(d);
        g.el.style.transition = 'none'; g.el.classList.add('dragging');
      }
      if (g.moved) {
        const br = r.getBoundingClientRect(), w = g.el._w, h = this.dh;
        g.x = e.clientX - br.left - w / 2; g.y = Math.max(0, Math.min(this.H - h, e.clientY - br.top - h / 2));
        g.el.style.transform = T(g.x, g.y);
        const t = this.towerAt(e.clientX);
        this.towers.forEach((tw, k) => tw.classList.toggle('sel', k === t));
      }
    });
    const end = e => {
      const g = this.drag; if (!g) return; this.drag = null;
      this.towers.forEach(t => t.classList.remove('sel'));
      if (!g.moved) { this.select(g.from); return; }
      const to = this.towerAt(e.clientX);
      g.el.classList.remove('dragging');
      if (to === g.from) { this.homeOf(g.from); return; }
      this.tryMove(g.from, to, { startPos: { x: g.x, y: g.y } });
    };
    r.addEventListener('pointerup', end);
    r.addEventListener('pointercancel', e => { const g = this.drag; if (g) { this.drag = null; this.homeOf(g.from); } });
  }
  destroy() {
    this.dead = true;
    this.anims.forEach(a => { try { a.cancel(); } catch (e) { /* ignore */ } });
    this.timers.forEach(clearTimeout);
    this.ro.disconnect(); this.root.remove();
  }
}

/* ---------------- E. live demo for the focused mode panel ---------------- */
const MODES = {};          // filled from /api/modes (par and limit come from Prolog)
const Demo = {
  board: null, token: 0, sound: false,
  start(mode, host) {
    this.stop();
    const tok = ++this.token, n = MODES[mode].discs;
    const b = new Board(host, mode, n, { ambCount: 7, sfx: (k, r) => { if (this.sound) Sound.play(k, mode, r); } });
    this.board = b; b.setPegs(initPegs(n));
    this.loop(tok, b, n);
  },
  stop() { this.token++; if (this.board) { this.board.destroy(); this.board = null; } },
  async loop(tok, b, n) {
    const plan = [];
    (function hanoi(k, f, t, v) { if (!k) return; hanoi(k - 1, f, v, t); plan.push([f, t]); hanoi(k - 1, v, t, f); })(n, 0, 2, 1);
    const dur = Math.max(110, 680 - n * 65);
    while (tok === this.token) {
      b.setPegs(initPegs(n));
      await sleep(900);
      for (const [f, t] of plan) {
        if (tok !== this.token) return;
        const after = b.pegs.map(x => x.slice()); after[t].push(after[f].pop());   // demo only: known optimal sequence
        await b.move(f, t, after, { dur });
      }
      await sleep(1800);
    }
  }
};

/* ---------------- F. screens and game controller ---------------- */
const ui = { mode: null, names: ['', '', '', ''], count: 1, players: [], basis: null, basisRandom: false, game: null, state: null, board: null, base: { ms: 0, at: 0, running: false }, ticker: 0 };
let currentScreen = 'screen-modes';

function show(id) {
  currentScreen = id;
  $$('.screen').forEach(s => s.classList.toggle('active', s.id === id));
  if (id !== 'screen-modes') Demo.stop();
  if (id !== 'screen-results') Party.stop();
}
const icon = k => el('span', { html: ICON[k] });

/* ----- screen 1: mode select ----- */
let focused = null, lastPointer = 'mouse';
function setFocus(p) {
  if (focused === p) return;
  focused = p;
  $$('.panel').forEach(x => x.classList.toggle('focus', x === p));
  $('#panels').classList.toggle('has-focus', !!p);
  Demo.stop();
  if (p && p.dataset.mode !== 'random') Demo.start(p.dataset.mode, $('.demo', p));
}
function buildModes() {
  const wrap = $('#panels'); wrap.innerHTML = ''; focused = null;
  [...MODE_ORDER, 'random'].forEach(key => {
    const t = THEME[key], m = MODES[key], rnd = key === 'random';
    const panel = el('div', { class: 'panel theme-' + key, 'data-mode': key, role: 'button', 'aria-label': t.name });
    panel.append(el('div', { class: 'strip' }, icon(key), el('span', { class: 'ttl', text: t.name }), el('span', { class: 'hint', text: rnd ? 'Hover to see' : t.tag })));
    const detail = el('div', { class: 'detail' });
    detail.append(el('h2', {}, icon(key), t.name));
    if (rnd) {
      detail.append(el('div', { class: 'qmark', text: '?' }), el('p', { class: 'tag', text: 'The tower is chosen for you when the game starts.' }));
    } else {
      detail.append(el('p', { class: 'tag', text: t.tag }),
        el('div', { class: 'chips' }, el('span', { class: 'chip', text: m.discs + ' discs' }), el('span', { class: 'chip', text: 'Par ' + m.par }), el('span', { class: 'chip', text: 'Limit ' + m.limit })),
        el('div', { class: 'demo' }));
      const btn = el('button', { class: 'snd', type: 'button', 'aria-pressed': 'false', text: 'Preview sound: off' });
      const swallow = e => e.stopPropagation();
      btn.addEventListener('pointerdown', swallow);
      btn.addEventListener('click', e => {
        e.stopPropagation(); Sound.unlock();
        Demo.sound = !Demo.sound;
        btn.textContent = 'Preview sound: ' + (Demo.sound ? 'on' : 'off'); btn.setAttribute('aria-pressed', Demo.sound);
        if (Demo.sound) Sound.play('land', key, 0.5);
      });
      detail.append(btn);
    }
    detail.append(el('div', { class: 'cta', text: 'Click to play' }));
    panel.append(detail);
    panel.addEventListener('pointerdown', e => { lastPointer = e.pointerType; });
    panel.addEventListener('pointerenter', e => { if (e.pointerType === 'mouse') setFocus(panel); });
    panel.addEventListener('click', () => {
      if (lastPointer === 'mouse' || panel === focused) selectMode(key); else setFocus(panel);
    });
    wrap.append(panel);
  });
}
function selectMode(key) { ui.mode = key; Demo.stop(); openPlayers(); }

/* ----- screen 2: players ----- */
function openPlayers() {
  $('#pl-mode').textContent = ui.mode === 'random' ? 'Mode: Random (revealed when the game starts)' : 'Mode: ' + THEME[ui.mode].name;
  renderPlayers(); show('screen-players');
}
function renderPlayers() {
  const multi = ui.count > 1;
  $('#seg-single').setAttribute('aria-pressed', !multi); $('#seg-multi').setAttribute('aria-pressed', multi);
  const cr = $('#count-row'); cr.hidden = !multi; cr.innerHTML = '';
  [2, 3, 4].forEach(n => cr.append(el('button', { type: 'button', 'aria-pressed': ui.count === n, text: n + ' players', onclick: () => { ui.count = n; renderPlayers(); } })));
  const box = $('#names'); box.innerHTML = '';
  for (let i = 0; i < ui.count; i++) {
    const inp = el('input', { type: 'text', maxlength: '24', autocomplete: 'off', value: ui.names[i], 'aria-label': 'Name of player ' + (i + 1) });
    inp.addEventListener('input', () => { ui.names[i] = inp.value; inp.removeAttribute('aria-invalid'); $('#name-error').textContent = ''; });
    box.append(el('label', { class: 'field' }, multi ? 'Player ' + (i + 1) + ' name' : 'Your name', inp));
  }
  $('#name-error').textContent = '';
}
function submitPlayers() {
  const names = ui.names.slice(0, ui.count).map(s => s.trim());
  const bad = names.findIndex(s => !s);
  if (bad >= 0) {
    const inputs = $$('#names input');
    inputs.forEach((x, i) => { if (!names[i]) x.setAttribute('aria-invalid', 'true'); });
    $('#name-error').textContent = ui.count > 1 ? 'Every player needs a name. Player ' + (bad + 1) + ' is empty.' : 'Please enter your name to continue.';
    inputs[bad].focus(); return;
  }
  ui.players = names; show('screen-basis'); $('#basis-msg').textContent = '';
  $$('.basis-card').forEach(b => { b.disabled = false; b.classList.remove('reveal'); });
}

/* ----- screen 3: basis ----- */
async function chooseBasis(kind) {
  ui.basisRandom = false;
  if (kind === 'random') {
    $$('.basis-card').forEach(b => b.disabled = true);
    const card = $('#basis-random'), label = $('b', card);
    card.classList.add('reveal'); Sound.play('reveal', 'easy');
    let r;
    try { r = await api('/api/random-basis'); } catch (e) { $('#basis-msg').textContent = 'Could not reach the server.'; $$('.basis-card').forEach(b => b.disabled = false); return; }
    const names = Object.values(BASIS_NAME); let i = 0;
    const iv = setInterval(() => { label.textContent = names[i++ % 2]; }, 150);
    await sleep(1500); clearInterval(iv);
    label.textContent = BASIS_NAME[r.basis]; $('#basis-msg').textContent = 'Picked for you: ' + BASIS_NAME[r.basis];
    await sleep(1300);
    label.textContent = 'Random'; card.classList.remove('reveal');
    ui.basis = r.basis; ui.basisRandom = true;
  } else ui.basis = kind;
  startGame();
}

/* ----- starting a game ----- */
async function startGame() {
  let r;
  try { r = await api('/api/new', { mode: ui.mode, players: ui.players, basis: ui.basis, basis_random: ui.basisRandom }); }
  catch (e) { alert('Could not start the game: ' + (e.message || e.error || 'server error')); show('screen-modes'); return; }
  ui.game = r.state.game; ui.state = r.state;
  if (r.state.mode_random) await revealMode(r.state.mode);
  enterPlay();
  await beginTurn();
}
async function revealMode(mode) {
  const rv = $('#reveal'); rv.className = ''; rv.innerHTML = '';
  const m = MODES[mode], t = THEME[mode];
  const card = el('div', { class: 'rcard' }, el('div', { class: 'rface front', text: '?' }),
    el('div', { class: 'rface back theme-' + mode }, icon(mode), t.name, el('small', { text: m.discs + ' discs' })));
  const back = $('.back', card); back.classList.add('panel');
  rv.append(card, el('p', { text: 'Choosing your tower...', style: 'font-size:1.3rem;margin:0' }));
  Sound.unlock(); Sound.play('reveal', 'easy');
  card.classList.add('spin'); await sleep(2300);
  $('p', rv).textContent = t.name + ': ' + m.discs + ' discs, par ' + m.par + ', limit ' + m.limit;
  await sleep(1500); rv.className = 'hidden';
}
async function beginTurn() {
  try { const r = await api('/api/begin', { game: ui.game }); applyState(r.state); } catch (e) { toast('Could not start the turn.'); }
}

/* ----- screen 4: play ----- */
function enterPlay() {
  const s = ui.state, host = $('#stage');
  if (ui.board) ui.board.destroy();
  host.innerHTML = '';
  ui.board = new Board(host, s.mode, s.discs, {
    interactive: true, ambCount: 16, onTry: tryMove,
    sfx: (k, r) => Sound.play(k, s.mode, r)
  });
  ui.board.setPegs(s.pegs);
  $('#r-ico').innerHTML = ICON[s.mode]; $('#r-ico svg').style.cssText = 'width:36px;height:36px';
  $('#r-mode').textContent = THEME[s.mode].name + (s.mode_random ? ' (random)' : '');
  $('#r-basis').textContent = 'Ranked by ' + BASIS_NAME[s.basis].toLowerCase() + (s.basis_random ? ' (random)' : '');
  $('#r-par').textContent = s.par; $('#r-limit').textContent = s.limit;
  ['b-undo', 'b-restart', 'b-pause'].forEach(id => $('#' + id).classList.toggle('hidden', s.multi));   // the server enforces this too
  show('screen-play');
  Sound.ambient(s.mode);
  clearInterval(ui.ticker); ui.ticker = setInterval(tick, 250);
}
function tick() {
  const b = ui.base;
  $('#r-time').textContent = fmtTime(b.ms + (b.running ? performance.now() - b.at : 0));
}
function applyState(s) {
  ui.state = s;
  ui.base = { ms: s.elapsed_ms, at: performance.now(), running: s.running };
  $('#r-moves').textContent = s.moves;
  $('#r-over').classList.toggle('hidden', !s.over_limit);
  $('#b-undo').disabled = !s.can_undo;
  $('#b-pause').textContent = s.status === 'paused' ? 'Resume' : 'Pause';
  const list = $('#r-players'); list.innerHTML = '';
  s.players.forEach((p, i) => {
    const res = s.results.find(r => r.index === i);
    list.append(el('li', { class: i === s.current && s.status !== 'finished' ? 'cur' : '' }, el('span', { text: p }),
      res ? el('span', { class: 'done', text: res.moves + ' / ' + fmtTime(res.time_ms) }) : ''));
  });
  if (ui.board) ui.board.locked = s.status === 'paused' || s.status === 'ready' || s.status === 'finished';
  const ov = $('#pause-ov');
  if (s.status === 'paused' && !ov) showPauseOverlay(); else if (s.status !== 'paused' && ov) ov.remove();
  tick();
}
function toast(msg, ms = 2200) {
  const t = el('div', { class: 'toast', role: 'status', text: msg }); $('#stage').append(t); setTimeout(() => t.remove(), ms);
}
function showPauseOverlay() {
  $('#stage').append(el('div', { class: 'overlay', id: 'pause-ov' }, el('h2', { text: 'Paused' }), el('p', { text: 'The timer is stopped and the board is hidden.' }),
    el('button', { class: 'btn', type: 'button', text: 'Resume', onclick: togglePause })));
}

async function tryMove(from, to, o) {
  const b = ui.board;
  try {
    const r = await api('/api/move', { game: ui.game, from, to });
    if (!r.finished) applyState(r.state); else $('#r-moves').textContent = r.moves;
    await b.move(from, to, r.pegs, o);
    if (r.finished) await playerFinished(r);
  } catch (err) {
    if (err.status === 422) b.reject(from, to);
    else { b.reject(from, to); toast(err.status === 0 ? 'Lost connection to the server.' : (err.message || 'Move refused.')); }
  }
}
async function playerFinished(r) {
  ui.base = { ms: r.result.time_ms, at: performance.now(), running: false }; tick();
  ui.board.locked = true;
  await sleep(700);
  const res = r.result;
  if (!r.game_over) {
    toast(res.player + ' solved it: ' + res.moves + ' moves, ' + fmtTime(res.time_ms) + ' ' + starText(res.stars), 2600);
    await sleep(2700);
    applyState(r.state);
    showPass(r.state);
  } else goResults();
}
function showPass(s) {
  $('#pass-name').textContent = s.current_name;
  $('#pass-info').textContent = 'Player ' + (s.current + 1) + ' of ' + s.players.length + '. Same puzzle, fresh board. Your timer starts when you press the button.';
  ui.board.setPegs(s.pegs);
  show('screen-pass');
}
async function togglePause() {
  if (ui.board.busy) return;
  try { const r = await api('/api/pause', { game: ui.game, paused: ui.state.status !== 'paused' }); applyState(r.state); } catch (e) { toast('Pause refused.'); }
}
async function doUndo() {
  if (ui.board.busy || ui.state.status !== 'playing') return;
  try {
    const r = await api('/api/undo', { game: ui.game });
    applyState(r.state);
    await ui.board.move(r.undone.to, r.undone.from, r.state.pegs, { dur: 420 });
  } catch (e) { ui.board.shake(); Sound.play('error'); }
}
async function doRestart() {
  if (ui.board.busy) return;
  try { const r = await api('/api/restart', { game: ui.game }); applyState(r.state); ui.board.setPegs(r.state.pegs); Sound.play('reveal', 'easy'); } catch (e) { toast('Restart refused.'); }
}
function leavePlay() { clearInterval(ui.ticker); Sound.stopAmbient(); if (ui.board) { ui.board.destroy(); ui.board = null; } }
function toMenu() { leavePlay(); ui.game = null; show('screen-modes'); buildModes(); }

/* ----- results ----- */
function renderLeaderboard(lb, mine) {
  const box = el('div', {});
  box.append(el('h3', { class: 'lbh', text: 'Leaderboard: ' + THEME[lb.mode].name + ', ' + BASIS_NAME[lb.basis].toLowerCase() }));
  if (!lb.entries.length) { box.append(el('p', { text: 'No scores yet.' })); return box; }
  const tb = el('table', { class: 'rank' }, el('tr', {}, ...['Rank', 'Name', 'Moves', 'Time', 'Stars'].map(h => el('th', { text: h }))));
  lb.entries.forEach(e => tb.append(el('tr', { class: mine && e.id.startsWith(mine + '-') ? 'me' : '' },
    el('td', { text: e.rank }), el('td', { text: e.name || e.player }), el('td', { text: e.moves + (e.over ? ' (over limit)' : '') }), el('td', { text: fmtTime(e.time_ms) }), el('td', { text: starText(e.stars) }))));
  box.append(el('div', { class: 'rank-wrap' }, tb)); return box;
}
async function goResults() {
  let f;
  try { f = await api('/api/finish', { game: ui.game }); } catch (e) { toast('Could not load the results.'); return; }
  leavePlay();
  const s = f.state, card = $('#res-card'); card.innerHTML = '';
  const modeLine = THEME[s.mode].name + (s.mode_random ? ' (random)' : '') + ' | ranked by ' + BASIS_NAME[s.basis].toLowerCase() + (s.basis_random ? ' (random)' : '');
  if (!s.multi) {
    const r = f.ranking[0];
    card.append(el('h1', { text: 'Congratulations, ' + r.player + '!' }), el('p', { class: 'sub', text: modeLine }),
      el('div', { class: 'stars', 'aria-label': r.stars + ' of 3 stars' }, ...[0, 1, 2].map(i => el('span', { class: i < r.stars ? '' : 'off', text: i < r.stars ? STAR_ON : STAR_OFF }))),
      el('div', { class: 'metrics' }, el('span', { text: r.moves + ' moves' }), el('span', { text: 'Time ' + fmtTime(r.time_ms) }), el('span', { text: 'Par ' + s.par }), el('span', { text: 'Limit ' + s.limit }),
        r.over ? el('span', { class: 'flag', text: 'OVER LIMIT' }) : null));
    Sound.play('fanfare', 'easy'); Party.start($('#party'));
  } else {
    const best = f.ranking.filter(r => r.rank === 1).map(r => r.player);
    card.append(el('h1', { text: best.length > 1 ? 'Shared first place' : 'Winner: ' + best[0] }), el('p', { class: 'sub', text: modeLine + (best.length > 1 ? ' | ' + best.join(' and ') : '') }));
    const tb = el('table', { class: 'rank' }, el('tr', {}, ...['Rank', 'Player', 'Moves', 'Time', 'Stars', 'Limit'].map(h => el('th', { text: h }))));
    f.ranking.forEach(r => tb.append(el('tr', {}, el('td', { text: r.rank }), el('td', { text: r.player }), el('td', { text: r.moves }), el('td', { text: fmtTime(r.time_ms) }),
      el('td', { text: starText(r.stars) }), el('td', { text: r.over ? 'OVER LIMIT' : 'ok', class: r.over ? 'flag' : '' }))));
    card.append(el('div', { class: 'rank-wrap' }, tb));
    Sound.play('fanfare', 'easy');
  }
  card.append(renderLeaderboard(f.leaderboard, ui.game),
    el('div', { class: 'row end' }, el('button', { class: 'btn', type: 'button', text: 'Play again', onclick: toMenu })));
  show('screen-results');
}

/* ----- leaderboard viewer ----- */
async function openLeaderboards() {
  let data;
  try { data = (await api('/api/leaderboard')).leaderboards; } catch (e) { return; }
  let mode = 'easy', basis = 'moves';
  const modal = $('#modal'); modal.classList.remove('hidden');
  const draw = () => {
    const card = el('div', { class: 'card' }, el('h1', { text: 'Leaderboards' }));
    const seg1 = el('div', { class: 'seg' }, ...MODE_ORDER.map(m => el('button', { type: 'button', 'aria-pressed': m === mode, text: THEME[m].name, onclick: () => { mode = m; draw(); } })));
    const seg2 = el('div', { class: 'seg', style: 'margin-top:8px' }, ...['moves', 'time'].map(b => el('button', { type: 'button', 'aria-pressed': b === basis, text: BASIS_NAME[b], onclick: () => { basis = b; draw(); } })));
    card.append(seg1, seg2, renderLeaderboard(data.find(x => x.mode === mode && x.basis === basis), null),
      el('div', { class: 'row end' }, el('button', { class: 'btn', type: 'button', text: 'Close', onclick: () => modal.classList.add('hidden') })));
    modal.innerHTML = ''; modal.append(card);
  };
  draw();
}

/* ---------------- G. celebration: fireworks, lanterns, petals ---------------- */
const Party = {
  raf: 0, parts: [], cv: null,
  start(cv) {
    this.stop(); this.cv = cv; const c = cv.getContext('2d'); let t = 0;
    const size = () => { const d = window.devicePixelRatio || 1; cv.width = innerWidth * d; cv.height = innerHeight * d; c.setTransform(d, 0, 0, d, 0, 0); };
    size(); this.onResize = size; addEventListener('resize', size);
    const frame = () => {
      t++; const W = innerWidth, H = innerHeight;
      if (t % 38 === 1) { const x = rand(W * 0.1, W * 0.9), y = rand(H * 0.1, H * 0.5), h = rand(0, 360);
        for (let i = 0; i < 46; i++) { const a = rand(0, 6.28), s = rand(1.2, 4.2); this.parts.push({ k: 'f', x, y, vx: Math.cos(a) * s, vy: Math.sin(a) * s, life: rand(60, 100), max: 100, h: h + rand(-25, 25) }); } }
      if (t % 55 === 0) this.parts.push({ k: 'l', x: rand(W * 0.05, W * 0.95), y: H + 30, vy: -rand(0.5, 1.1), ph: rand(0, 6), life: 9999 });
      if (t % 9 === 0) this.parts.push({ k: 'p', x: rand(0, W), y: -10, vy: rand(1, 2), ph: rand(0, 6), life: 9999, r: rand(0, 6) });
      c.clearRect(0, 0, W, H);
      this.parts = this.parts.filter(p => {
        if (p.k === 'f') { p.x += p.vx; p.y += p.vy; p.vy += 0.045; p.vx *= 0.99; p.life--; c.globalAlpha = Math.max(0, p.life / p.max); c.fillStyle = 'hsl(' + p.h + ' 100% 65%)'; c.beginPath(); c.arc(p.x, p.y, 2.4, 0, 6.28); c.fill(); return p.life > 0; }
        if (p.k === 'l') { p.y += p.vy; p.x += Math.sin(p.ph + t / 40) * 0.5; c.globalAlpha = 0.95; c.shadowColor = '#ff8a3a'; c.shadowBlur = 18; c.fillStyle = '#ff7a30'; c.fillRect(p.x - 9, p.y - 13, 18, 26); c.fillStyle = '#ffd27a'; c.fillRect(p.x - 5, p.y - 8, 10, 16); c.shadowBlur = 0; return p.y > -40; }
        p.y += p.vy; p.x += Math.sin(p.ph + t / 30) * 0.9; c.globalAlpha = 0.85; c.fillStyle = '#f7a8bd'; c.beginPath(); c.ellipse(p.x, p.y, 7, 4, p.r + t / 25, 0, 6.28); c.fill(); return p.y < H + 20;
      });
      c.globalAlpha = 1; this.raf = requestAnimationFrame(frame);
    };
    frame();
  },
  stop() { cancelAnimationFrame(this.raf); this.raf = 0; this.parts = []; if (this.onResize) { removeEventListener('resize', this.onResize); this.onResize = null; } if (this.cv) this.cv.getContext('2d').clearRect(0, 0, this.cv.width, this.cv.height); }
};

/* ---------------- boot ---------------- */
async function boot() {
  try { (await api('/api/modes')).modes.forEach(m => { MODES[m.id] = m; }); }
  catch (e) { document.body.append(el('p', { text: 'Cannot reach the Prolog server.', style: 'color:#fff;padding:20px' })); return; }
  buildModes();
  $('#seg-single').onclick = () => { ui.count = 1; renderPlayers(); };
  $('#seg-multi').onclick = () => { ui.count = Math.max(2, ui.count); renderPlayers(); };
  $('#pl-back').onclick = () => { show('screen-modes'); buildModes(); };
  $('#pl-next').onclick = submitPlayers;
  $('#ba-back').onclick = () => show('screen-players');
  $$('.basis-card').forEach(b => b.onclick = () => chooseBasis(b.dataset.basis));
  $('#b-undo').onclick = doUndo; $('#b-restart').onclick = doRestart; $('#b-pause').onclick = togglePause;
  $('#b-sound').onclick = () => { Sound.unlock(); const on = !Sound.isEnabled(); Sound.setEnabled(on); $('#b-sound').textContent = 'Sound: ' + (on ? 'on' : 'off'); if (on && ui.state) Sound.ambient(ui.state.mode); };
  $('#b-menu').onclick = () => { if (confirm('Leave this game?')) toMenu(); };
  $('#pass-go').onclick = async () => { Sound.unlock(); show('screen-play'); await beginTurn(); };
  $('#btn-lb').onclick = openLeaderboards;
}
boot();
|}).
