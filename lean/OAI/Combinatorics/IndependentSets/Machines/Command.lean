import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.TableIterationFiniteAlphabet

namespace OAI

namespace IndependentSetsCut.CounterMachine
variable {R L : Type} [DecidableEq R]

inductive Command (R : Type) where
  | skip
  | inc (r : R)
  | dec (r : R)
  | write (b : Bool)
  | discard
  | rewind
  | seq (first second : Command R)
  | test (r : R) (zero positive : Command R)
  | read (one zero empty : Command R)
  | loop (r : R) (body : Command R)

namespace Command

def Label : Command R → Type
  | .skip | .inc _ | .dec _ | .write _ | .discard | .rewind => Unit
  | .seq a b => Label a ⊕ Label b
  | .test _ a b => Unit ⊕ Label a ⊕ Label b
  | .read a b c => Unit ⊕ Label a ⊕ Label b ⊕ Label c
  | .loop _ b => Unit ⊕ Label b

noncomputable instance labelFintype (c : Command R) : Fintype (Label c) := by
  induction c with
  | skip | inc | dec | write | discard | rewind => exact inferInstanceAs (Fintype Unit)
  | seq a b ia ib => exact inferInstanceAs (Fintype (Label a ⊕ Label b))
  | test r a b ia ib => exact inferInstanceAs (Fintype (Unit ⊕ Label a ⊕ Label b))
  | read a b c ia ib ic => exact inferInstanceAs (Fintype (Unit ⊕ Label a ⊕ Label b ⊕ Label c))
  | loop r b ib => exact inferInstanceAs (Fintype (Unit ⊕ Label b))

def entry : (c : Command R) → Label c
  | .skip | .inc _ | .dec _ | .write _ | .discard | .rewind => ()
  | .seq a _ => .inl a.entry
  | .test _ _ _ | .read _ _ _ | .loop _ _ => .inl ()

def code : (c : Command R) → (Label c → L) → L → Label c → Instruction R L
  | .skip, _, exit, _ => .jump exit
  | .inc r, _, exit, _ => .inc r exit
  | .dec r, _, exit, _ => .dec r exit exit
  | .write b, _, exit, _ => .write b exit
  | .discard, _, exit, _ => .discard exit
  | .rewind, labels, exit, _ => .back (labels ()) exit
  | .seq a b, labels, _exit, .inl l =>
      a.code (fun l => labels (.inl l)) (labels (.inr b.entry)) l
  | .seq _a b, labels, exit, .inr l => b.code (fun l => labels (.inr l)) exit l
  | .test r a b, labels, _, .inl _ =>
      .test r (labels (.inr (.inl a.entry))) (labels (.inr (.inr b.entry)))
  | .test _ a _, labels, exit, .inr (.inl l) =>
      a.code (fun l => labels (.inr (.inl l))) exit l
  | .test _ _ b, labels, exit, .inr (.inr l) =>
      b.code (fun l => labels (.inr (.inr l))) exit l
  | .read a b c, labels, _, .inl _ =>
      .read (labels (.inr (.inl a.entry))) (labels (.inr (.inr (.inl b.entry))))
        (labels (.inr (.inr (.inr c.entry))))
  | .read a _ _, labels, exit, .inr (.inl l) =>
      a.code (fun l => labels (.inr (.inl l))) exit l
  | .read _ b _, labels, exit, .inr (.inr (.inl l)) =>
      b.code (fun l => labels (.inr (.inr (.inl l)))) exit l
  | .read _ _ c, labels, exit, .inr (.inr (.inr l)) =>
      c.code (fun l => labels (.inr (.inr (.inr l)))) exit l
  | .loop r b, labels, exit, .inl _ => .dec r (labels (.inr b.entry)) exit
  | .loop _ b, labels, _, .inr l => b.code (fun l => labels (.inr l)) (labels (.inl ())) l

def incData (d : Data R) (r : R) : Data R :=
  { d with reg := Function.update d.reg r (d.reg r + 1) }
def decData (d : Data R) (r : R) : Data R :=
  { d with reg := Function.update d.reg r (d.reg r - 1) }
def readData (d : Data R) : Data R :=
  { d with input := d.input.tail, backup := d.input.take 1 ++ d.backup }
def backData (d : Data R) : Data R :=
  { d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail }
def discardData (d : Data R) : Data R := {d with input := d.input.tail}
def writeData (d : Data R) (b : Bool) : Data R := { d with output := b :: d.output }

inductive Evaluates : Command R → Data R → Data R → ℕ → Prop
  | skip (d) : Evaluates .skip d d 1
  | inc (d r) : Evaluates (.inc r) d (incData d r) 1
  | dec (d r) : Evaluates (.dec r) d (decData d r) 1
  | write (d b) : Evaluates (.write b) d (writeData d b) 1
  | discard (d) : Evaluates .discard d (discardData d) 1
  | rewind_empty {d} : d.backup = [] → Evaluates .rewind d d 1
  | rewind_cons {d e n b rest} : d.backup = b :: rest →
      Evaluates .rewind (backData d) e n → Evaluates .rewind d e (1 + n)
  | seq {a b d e f n m} : Evaluates a d e n → Evaluates b e f m →
      Evaluates (.seq a b) d f (n + m)
  | test_zero {r a b d e n} : d.reg r = 0 → Evaluates a d e n →
      Evaluates (.test r a b) d e (1 + n)
  | test_pos {r a b d e n} : d.reg r ≠ 0 → Evaluates b d e n →
      Evaluates (.test r a b) d e (1 + n)
  | read_one {a b c d e n rest} : d.input = true :: rest →
      Evaluates a (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | read_zero {a b c d e n rest} : d.input = false :: rest →
      Evaluates b (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | read_empty {a b c d e n} : d.input = [] →
      Evaluates c (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | loop_zero {r b d} : d.reg r = 0 → Evaluates (.loop r b) d d 1
  | loop_pos {r b d e f n m} : d.reg r ≠ 0 →
      Evaluates b (decData d r) e n → Evaluates (.loop r b) e f m →
      Evaluates (.loop r b) d f (1 + n + m)

end Command

def advance (p : L → Instruction R L) : Option (Configuration R L) → Option (Configuration R L) :=
  fun c => c.bind (step p)

def atCfg (l : L) (d : Data R) : Option (Configuration R L) := some ⟨d, some l⟩

def Runs (p : L → Instruction R L) (n : ℕ) (l : L) (d : Data R) (l' : L) (d' : Data R) : Prop :=
  (advance p)^[n] (atCfg l d) = atCfg l' d'

 theorem runs_one (p : L → Instruction R L) (l : L) (d : Data R) (l' : L) (d' : Data R)
    (h : (p l).execute d = ⟨d', some l'⟩) : Runs p 1 l d l' d' := by
  simpa [Runs, advance, atCfg, step] using congrArg some h

 theorem Runs.trans {p : L → Instruction R L} {n m : ℕ} {l l' l'' : L} {d e f : Data R}
    (h : Runs p n l d l' e) (h' : Runs p m l' e l'' f) : Runs p (n + m) l d l'' f := by
  unfold Runs at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h, h']

namespace Command
 theorem trace {c : Command R} {d d' : Data R} {n : ℕ} (h : Evaluates c d d' n)
    (p : L → Instruction R L) (labels : c.Label → L) (exit : L)
    (atLabels : ∀ l, p (labels l) = c.code labels exit l) :
    Runs p n (labels c.entry) d exit d' := by
  induction h generalizing L with
  | skip d =>
    apply runs_one
    rw [atLabels]; rfl
  | inc d r =>
    apply runs_one
    rw [atLabels]; rfl
  | dec d r =>
    apply runs_one
    rw [atLabels]
    simp [code, Instruction.execute, decData]
  | write d b =>
    apply runs_one
    rw [atLabels]; rfl
  | discard d =>
    apply runs_one
    rw [atLabels]; rfl
  | @rewind_empty d hd =>
    apply runs_one
    rw [atLabels]
    simp [code, Instruction.execute, hd]
    cases d; simp_all
  | @rewind_cons d e n b rest hd he ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p labels exit atLabels)
    rw [atLabels]
    simp [code, entry, Instruction.execute, backData, hd]
  | @seq a b d e f n m h h' ih ih' =>
    exact Runs.trans
      (ih p (fun l => labels (.inl l)) (labels (.inr b.entry)) (fun l => atLabels (.inl l)))
      (ih' p (fun l => labels (.inr l)) exit (fun l => atLabels (.inr l)))
  | @test_zero r a b d e n hr h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inl l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
  | @test_pos r a b d e n hr h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
  | @read_one a b c d e n rest hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inl l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @read_zero a b c d e n rest hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr (.inl l)))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @read_empty a b c d e n hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr (.inr l)))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @loop_zero r b d hr =>
    apply runs_one
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
    rw [← hr, Function.update_eq_self]
  | @loop_pos r b d e f n m hr h h' ih ih' =>
    refine Runs.trans (Runs.trans (runs_one p _ _ _ _ ?_)
      (ih p (fun l => labels (.inr l)) (labels (.inl ())) (fun l => atLabels (.inr l))))
        (ih' p labels exit atLabels)
    rw [atLabels]
    simp [code, entry, Instruction.execute, decData, hr]
end Command
end IndependentSetsCut.CounterMachine

end OAI
