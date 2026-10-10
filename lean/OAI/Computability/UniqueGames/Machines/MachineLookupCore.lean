import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.PCP.SourceMachine

namespace OAI

/-!
Finite control for destructive unary-indexed table lookup. The guard decreases
the index even when the table is exhausted. Selection tests for an empty table
before writing the destination. All tests inspect just one finite head register.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def discard (source : K) (loopLabel returnLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.goto fun _ => loopLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => returnLabel)))

/-- Check that a field exists before seeding its destination delimiter. -/
def select (source destination : K) (copyLabel rejected : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (Hastad.SourceMachine.fieldStart destination copyLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => rejected)))

inductive Label
  | guard | skip | select | copy | accepted | rejected
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .skip, .select, .copy, .accepted,
  .rejected]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

/-- Six fixed labels and a single optional-bit register, independent of input. -/
def program (index source destination : K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard index .skip .select
  | .skip => discard source .skip .guard
  | .select => select source destination .copy .rejected
  | .copy => Hastad.SourceMachine.fieldLoop source destination .copy (some .accepted)
  | .accepted => .halt
  | .rejected => .halt

/-- Three caller tapes with every other tape retained verbatim. -/
def tapes (index source destination : K) (base : K → List Bool)
    (counter input output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base index counter) source input)
    destination output

@[simp] theorem tapes_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output index = counter := by
  simp [tapes, his, hid]

@[simp] theorem tapes_source (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) :
    tapes index source destination base counter input output source = input := by
  simp [tapes, hsd]

@[simp] theorem tapes_destination (index source destination : K)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output destination = output := by
  simp [tapes]

theorem tapes_other (index source destination p : K)
    (hi : p ≠ index) (hs : p ≠ source) (hd : p ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output p = base p := by
  simp [tapes, hi, hs, hd]

theorem update_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output) index replacement =
      tapes index source destination base replacement input output := by
  funext p
  by_cases hi : p = index
  · subst p; simp [tapes, his, hid]
  · by_cases hs : p = source
    · subst p; by_cases hs : source = destination <;> simp [tapes, hi, hs, Ne.symm hid]
    · by_cases hd : p = destination
      · subst p; simp [tapes, hi]
      · simp [tapes, hi, hs, hd]

theorem update_source (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output) source replacement =
      tapes index source destination base counter replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [tapes, hsd]
  · by_cases hd : p = destination
    · subst p; simp [tapes, hs]
    · simp [tapes, hs, hd]

theorem update_destination (index source destination : K)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output)
      destination replacement = tapes index source destination base counter input replacement := by
  simp [tapes]

theorem fieldTapes_eq (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output input' output' : List Bool) :
    Hastad.SourceMachine.fieldTapes source destination
      (tapes index source destination base counter input output) input' output' =
      tapes index source destination base counter input' output' := by
  rw [Hastad.SourceMachine.fieldTapes, update_source _ _ _ hsd, update_destination]

/-- A concrete finite machine using exactly three binary stacks. Its table and
unary index may be supplied in a caller configuration; no list oracle is used. -/
def machine : FinTM2 where
  K := Fin 3
  k₀ := 1
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .guard
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program 0 1 2

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

end OAI
