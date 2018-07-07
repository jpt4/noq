(*noq5.v
  20180622Z
  jpt4
  Nock5 in Coq*)

Inductive noun := 
  | atom : nat -> noun
  | cell : noun -> noun -> noun.
                         
Definition get_atom (a:noun) : nat :=
  match a with
  | atom a' => a'
  | cell _ _ => 0 
  end.

Compute get_atom (atom 5).
Compute (cell (cell (atom 6) (atom 11)) (atom 10)).

Notation "'%' x" := (atom x)
                     (at level 51, right associativity).

Notation "'[' x y ']'" := 
  (cell x y)
    (at level 50, right associativity).

Check [%3 %4].
Check [[%3 [%10 %11]] %2].
Compute 4 + 5 + 6 + 8.


Inductive wut :=
  wt : Noun -> wut.
Compute wt (a 5).

Definition nock := 
  

Fixpoint nock5 (n:nock) : Noun :=
  match n with 
  | wt (c a' b') => (a 0)
  | wt (a n') => (a 1)                   
 end.
