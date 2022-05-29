/*  Marcin Malejky                         (Tested under SICStus Prolog 4.6.0)*

    Deterministic finite automaton (DFA) is represented by the following term
        dfa(TransFun, StartSt, AcceptSts), where:
    TransFun  - list of possible transitions, each in the form of:
        fp(InitalState, Character, FinalState)
    StartSt   - Initial state of DFA.
    AcceptSts - List of accept states of DFA.

    Automaton representation I have adopted is in the form of:
        rep(Alphabet, FunT, AccpT), where
    Alphabet - unordered list of unique alphabet letters of the automaton
    FunT     - transition function represented as balanced BST**
    AccpT    - accepting states represented as balanced BST**

    * Requires lists module (usage: | ?- use_module(library(lists)).)
    * BST - binary search tree                                               */


% Sample correct automatons
example(a11, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1)],  % L={a,b}*
    1, [2,1])).
example(a12, dfa([fp(x,a,y),fp(x,b,x),fp(y,a,x),fp(y,b,x)],  % L={a,b}*
    x, [x,y])).
example(a2, dfa([fp(1,a,2),fp(2,b,1),fp(1,b,3),fp(2,a,3),    % L=(ab)^n
    fp(3,b,3),fp(3,a,3)], 1, [1])).
example(a3, dfa([fp(0,a,1),fp(1,a,0)], 0, [0])).             % L=(aa)^n
example(a4, dfa([fp(x,a,y),fp(y,a,z),fp(z,a,x)], x, [x])).   % L=(aaa)^n
example(a5, dfa([fp(x,a,y),fp(y,a,z),fp(z,a,zz),fp(zz,a,x)], % L=(aaaa)^n
    x, [x])).
example(a6, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1)],   % empty L
    1, [])).
example(a7, dfa([fp(1,a,1),fp(1,b,2),fp(2,a,2),fp(2,b,1),    % empty L
    fp(3,b,3),fp(3,a,3)], 1, [3])).

% Sample wrong automatons
example(b1, dfa([fp(1,a,1),fp(1,a,1)], 1, [])). % TransFun not a function
example(b2, dfa([fp(1,a,1),fp(1,a,2)], 1, [])). % TransFun not a total function
example(b3, dfa([fp(1,a,2)], 1, [])).           % -"-
example(b4, dfa([fp(1,a,1)], 2, [])).           % -"-
example(b5, dfa([fp(1,a,1)], 1, [1,2])).        % -"-
example(b6, dfa([], [], [])).                   % Empty alphabet


% Quicksort
qsort([],[]).
qsort([X | XS], Result) :-
    partition(XS, X, Left, Right),
    qsort(Left, L),
    qsort(Right, R),
    append(L, [X | R], Result).

partition([], _, [], []).
partition([X | XS], Pivot, [X | LS], RS) :-
    X @=< Pivot, partition(XS, Pivot, LS, RS).
partition([X | XS], Pivot, LS, [X | RS]) :-
    X @> Pivot, partition(XS, Pivot, LS, RS).

% Convert list to balanced BST
toTree(L, Result) :-
    qsort(L, SortedL),
    toTree_(SortedL, Result).
toTree_([], nil).
toTree_(L, tree(Value, LeftT, RightT)) :-
    length(L, Len),
    LeftLen is (Len // 2) + (Len mod 2) - 1,
    append_length(Left, [Value | Right], L, LeftLen),
    toTree_(Left, LeftT),
    toTree_(Right, RightT).

% Insert into BST, duplicates are ignored
insertT(X, nil, tree(X, nil, nil)).
insertT(X, tree(X, LeftT, RightT), tree(X, LeftT, RightT)).
insertT(X, tree(Y, LeftT, RightT), tree(Y, NewLeftT, RightT)) :-
    insertT(X, LeftT, NewLeftT),
    X @< Y.
insertT(X, tree(Y, LeftT, RightT), tree(Y, LeftT, NewRightT)) :-
    insertT(X, RightT, NewRightT),
    X @> Y.

% Check membership to BST
memberT(X, tree(X, _, _)).
memberT(X, tree(Y, LeftT, _)) :- memberT(X, LeftT), X @< Y.
memberT(X, tree(Y, _, RightT)) :- memberT(X, RightT), X @> Y.


% Get states occuring in the automaton
states(dfa(TransFun, StartSt, AcceptSts), Result) :-
    states(TransFun, TransStates),
    append(TransStates, [StartSt | AcceptSts], States),
    remove_dups(States, Result).
states([], []).
states([fp(S1, _, S2) | Rest], [S1, S2 | ResultRest]) :-
    states(Rest, ResultRest).

% Get alphabet of the automaton
alphabet(dfa(TransFun, _, _), Result) :-
    alphabet(TransFun, Letters),
    remove_dups(Letters, Result).
alphabet([], []).
alphabet([fp(_, C, _) | Rest], [C | ResultRest]) :-
    alphabet(Rest, ResultRest).

% Get all pairs (State, Letter) from the transition function
allPairs([], []).
allPairs([fp(S, C, _) | Rest], [pair(S, C) | ResultRest]) :-
    allPairs(Rest, ResultRest).

% Check whether the automaton is correct
correct(dfa(TransFun, StartSt, AcceptSts), rep(Alph, FunT, AccpT)) :-
    A = dfa(TransFun, StartSt, AcceptSts),
    alphabet(A, Alph), states(A, Sts), % Get the representation
    length(Alph, ALen), ALen > 0, % Check if the alphabet is not empty
    allPairs(TransFun, Pairs),
    remove_dups(Pairs, PairsSet),
    permutation(PairsSet, Pairs), % Check if TransFun is function
    length(Sts, SLen),
    Res is ALen*SLen,
    length(PairsSet, Res), % Check if TransFun is total function
    toTree(TransFun, FunT),
    toTree(AcceptSts, AccpT).

% Check whether the automaton accepts a word
accept(A, Word) :- correct(A, Rep), accept_(A, Word, Rep).
accept_(dfa(_, StartSt, _), [], rep(_, _, AccpT)) :-
    memberT(StartSt, AccpT).
accept_(dfa(TransFun, StartSt, AcceptSts), [X|XS], rep(Alph, FunT, AccpT)) :-
/* Order of operations here is important. "memberT" as the last
   statement ensure that backtracking will check other transitions
   first, and then check if word can be extended. */
    accept_(dfa(TransFun, N, AcceptSts), XS, rep(Alph, FunT, AccpT)),
    memberT(fp(StartSt, X, N), FunT).

% Check whether the language recognized by the automaton is empty
empty(A) :- correct(A, Rep), empty_(A, Rep).
empty_(dfa(_, _, []), _) :- !.
empty_(A, Rep) :- \+ search(A, nil, Rep).

% Search for the first accepting sequence
search(dfa(_, StartSt, _), _, rep(_, _, AccpT)) :-
    memberT(StartSt, AccpT), !.
search(dfa(TransFun, StartSt, AcceptSts), VisitedT, rep(Alph, FunT, AccpT)) :-
    \+ memberT(StartSt, VisitedT),
    memberT(fp(StartSt, _, N), FunT),
    insertT(StartSt, VisitedT, NewVisitedT),
    search(dfa(TransFun, N, AcceptSts), NewVisitedT, rep(Alph, FunT, AccpT)).

% Check if languages of the automatons are equal
equal(A1, A2) :-
    correct(A1, R1),
    correct(A2, R2),
    subsetEq_(A1, R1, A2, R2),
    subsetEq_(A2, R2, A1, R1).

% Check if language of the automaton is subset of the other
subsetEq(A1, A2) :-
    correct(A1, R1),
    correct(A2, R2),
    subsetEq_(A1, R1, A2, R2).
subsetEq_(A1, rep(Alph1, FunT1, _), A2, rep(Alph2, _, AccpT2)) :-
    permutation(Alph1, Alph2),
    complement(A2, AccpT2, CA2),
    correct(CA2, rep(_, FunT3, _)),
    intersection(CA2, FunT3, A1, FunT1, Intersect, IntFunT),
    dfa(_, _, IntAcceptSts) = Intersect,
    toTree(IntAcceptSts, IntAccpT),
    empty_(Intersect, rep([], IntFunT, IntAccpT)).

% "memberT" function with parameters swapped
memberTSwap(Tree, Elem) :- memberT(Elem, Tree).

% Get complement of the automaton
complement(dfa(TransFun, StartSt, AcceptSts), AccpT,
           dfa(TransFun, StartSt, NewAcceptSts)) :-
    A = dfa(TransFun, StartSt, AcceptSts),
    states(A, States),
    exclude(memberTSwap(AccpT), States, NewAcceptSts).

% Get cartesian product of the two lists
product(L1, L2, Result) :- product(L1, L2, Result, L1).
product(_, [], [], _).
product([], [_|T2], Result, L1) :-
    product(L1, T2, Result, _).
product([H1|T1], [H2|T2], [pair(H1,H2) | ResultRest], L1) :-
    product(T1, [H2|T2], ResultRest, L1).

% Get all intersection transitions
crossTrans(FunT1, FunT2, AccT, Result) :-
    memberT(fp(S11, C, S21), FunT1),
    memberT(fp(S12, C, S22), FunT2),
    Transition = fp(pair(S11, S12), C, pair(S21, S22)),
    \+ memberT(Transition, AccT), !,
    insertT(Transition, AccT, NewAccT),
    crossTrans(FunT1, FunT2, NewAccT, Result).
crossTrans(_, _, Result, Result).

% Get intersection of the two automatons
intersection(dfa(_, I1, AcceptSts1), FunT1,
             dfa(_, I2, AcceptSts2), FunT2, Result, FunT3) :-
    product(AcceptSts1, AcceptSts2, NewAcceptSts),
    crossTrans(FunT1, FunT2, nil, FunT3),
    Result = dfa([], pair(I1, I2), NewAcceptSts).

runTests :-
    % Load examples
    example(a11, A11), example(a12, A12),
    example(a2, A2), example(a3, A3), example(a4, A4),
    example(a5, A5), example(a6, A6), example(a7, A7),
    example(b1, B1), example(b2, B2), example(b3, B3),
    example(b4, B4), example(b5, B5), example(b6, B6),
    % Tests that should succeed
    correct(A11, _), correct(A12, _),
    correct(A2, _), correct(A3, _), correct(A4, _),
    correct(A5, _), correct(A6, _), correct(A7, _),
    equal(A11, A12),
    subsetEq(A2, A11),
    subsetEq(A5, A3),
    empty(A6),
    empty(A7),
    accept(A2, []),
    accept(A2, [a,b]),
    accept(A2, [a,b,a,b]),
    % Tests that should fail
    \+ correct(B1, _), \+ correct(B2, _), \+ correct(B3, _),
    \+ correct(B4, _), \+ correct(B5, _), \+ correct(B6, _),
    \+ empty(A11), \+ empty(A12), \+ empty(A2),
    \+ empty(A3), \+ empty(A4), \+ empty(A5),
    \+ equal(A3, A4),
    \+ subsetEq(A4, A3),
    \+ accept(A2, [a]).
