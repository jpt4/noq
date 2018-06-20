(** Homework Assignment 0#<br>#
#<a href="http://www.cs.berkeley.edu/~adamc/itp/">#Interactive Computer Theorem
Proving#</a><br>#
CS294-9, Fall 2006#<br>#
UC Berkeley *)

(** * Installing Coq *)

(** This section deals with getting Coq, the main tool we'll use in this class,
  up and running.
  - #<a href="http://coq.inria.fr/distrib-eng.html">#Download Coq version
    8.0#</a># from #<a href="http://coq.inria.fr/">#the Coq web site#</a>#.
    -- Version 8.1 might work for what we'll do in this class, but I haven't
       tried it yet.
    -- For any #<a href="http://www.debian.org/">#Debian Linux#</a># fans out
       there, there are
       #<a href="http://packages.debian.org/stable/math/coq">#Coq Debian
       packages#</a># that aren't mentioned on the Coq download page.
  - Following the installation instructions, you should end up with a
    #<tt>#coqtop#</tt># program that you can invoke from a command-line.  This
    is the simplest, text-based interface to Coq.  Try running
    #<tt>#coqtop#</tt># and stepping through the following interactive session,
    where the text on lines after #&lt;# prompts is for you to enter, and the
    rest should be produced by #<tt>#coqtop#</tt>#.
<<
Welcome to Coq 8.0pl3 (Jan 2006)

Coq < Check (1 + 1 = 2).
1 + 1 = 2
     : Prop

Coq < Goal (1 + 1 = 2).
1 subgoal
  
  ============================
   1 + 1 = 2

Unnamed_thm < trivial.
Proof completed.

Unnamed_thm < Qed.
trivial.
Unnamed_thm is defined

Coq < ^D
>>
  *)

(** * The Proof General Emacs mode *)

(**
  - I'm going to run briefly through how to use a particular "IDE" of sorts for
    Coq.  I use
    #<a href="http://proofgeneral.inf.ed.ac.uk/download">#Proof General#</a>#
    (#<a href="http://packages.debian.org/stable/editors/proofgeneral-coq">#Debian
    package#</a>#),
    an Emacs mode that supports a number of proof assistants.  There's also
    CoqIDE, the "official" IDE that is distributed with Coq.  I started using
    Proof General before CoqIDE was available and never switched, so I can't
    offer much advice on it.  You might want to try both, but, in any case,
    having something beyond #<tt>#coqtop#</tt>#'s console interface is seriously
    beneficial.  Without one, using Coq will feel like programming with
    #<tt>#ed#</tt>#.
  - Let's walk through an example with Proof
    General.  The HTML file you're reading was actually generated from a Coq
    source file. #<a href="HW0.v">#Download it#</a># to some convenient
    location.  Assuming you've installed Proof General for your preferred Emacs,
    you should be able to open the HW0.v file and see a fancy Proof General
    splash screen, followed by a syntax-highlighted display of that source file.
  - Press C-c . to turn on "electric period" mode, where every press of the
    period key is used to signal that you've finished entering a command.
  - Move to the end of the following definition of a list datatype and press the
    period key.  The definition should be accepted, as indicated by a message in
    a new buffer that is opened.  A general note about this section is that I'm
    not expecting you to understand what this code means, but rather just to get
    a feel for the Proof General interaction process.
  *)

Inductive list : Set :=
  | nil : list
  | cons : nat -> list -> list.

(** Do the same for this recursive definition of a list append function. *)

Fixpoint append (ls1 ls2 : list) {struct ls1} : list :=
  match ls1 with
    | nil => ls2
    | cons x ls1' => cons x (append ls1' ls2)
  end.

(** Now let's prove that [append] is associative.  Move the cursor after the
  period in the following [Theorem] command and press the period key.
  *)

Theorem append_associative : forall ls1 ls2 ls3,
  append (append ls1 ls2) ls3 = append ls1 (append ls2 ls3).

(** In the other buffer, you should see a representation of the initial proof
  state.  The formula we want to prove is displayed below a double-dashed line.
  We need to specify #<i>#tactics#</i># to direct Coq in performing the proof.
  Hit the period key at the end of the next line to send the first batch of
  instructions, which say that we want to proceed by induction on the first
  quantified argument [ls1].
  *)

  induction ls1; simpl; intros.

(** You should now see two subgoals displayed in the other buffer; one for the
  base ([nil]) case of the proof and one for the inductive ([cons]) case.  Now
  we have some named variables appearing above the double-dashed line.  Their
  presence tells us that we need to prove the formula for #<i>#any#</i># values
  of those variables.  You can probably see that the formula in this case is
  obviously true, so advance the proof by hitting period at the end of the next
  line.
  *)

  trivial.

(** In a less trivial case, we might have made a mistake and wish to back up.
  Position the cursor at the #<i>#start#</i># of the previous proof line and
  press C-c C-RET to undo the proof interaction back to that point.  After
  undoing, you can advance forward again by hitting the period key at the end of
  the line you want to return to, or by using C-c C-RET again with the cursor
  positioned anywhere on the line to fast-forward to.

  Now we're ready to finish the proof.  If you haven't already, fast-forward the
  proof state back to directly after the lone [trivial] tactic.  This leaves us
  with the task of giving the inductive step of the proof.

  We have our most complicated proof state yet.  Not only are there variables of
  types [nat] and [list] above the double line, but we also have a logical
  assumption [IHls1] that expresses the induction hypothesis.  We can finish the
  proof by rewriting the goal using the IH's quantified equality:
  *)

  rewrite IHls1; trivial.

(** Finally, we add this named theorem to the environment: *)
Qed.

Print append_associative.

(** And that's that.  There's no need to "turn in" this assignment, but
  definitely #<a href="mailto:adamc@cs.berkeley.edu">#let me know#</a># if you
  run into any problems getting this basic interaction to work.
  *)
