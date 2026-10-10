import Mathlib.Basic.Finite.Sigma
import OAI.Computability.UniqueGames.Machines.GraphCounterStartLemmas
import OAI.Computability.UniqueGames.Machines.MachineRepeat
import OAI.Computability.UniqueGames.Model

namespace OAI

section

/-!
Finiteness of every alphabet of the actual machines used by the reduction.
`FinTM2` already bundles finitely many tapes, control labels and register states,
but its alphabet field only requires the input tape alphabet to be finite.
This additional property is preserved by the actual sequential and repetition
constructors; it does not replace or alter their execution certificates.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

open Turing

/-! Every physical tape has a finite alphabet. Together with `M.kFin`, this
also makes the disjoint union of all physical tape alphabets finite. -/

/-- This one alphabet is already finite in the underlying machine record. -/
theorem input_finite (M : FinTM2) : Finite (M.Γ M.k₀) := by
  let := M.Γk₀Fin
  infer_instance

theorem of_homogeneous (M : FinTM2) {α : Type} [Finite α]
    (alphabet : ∀ k, M.Γ k = α) : FiniteAlphabet M := by
  intro k
  rw [alphabet k]
  infer_instance

/-- All concrete Boolean-stack machines satisfy the stronger alphabet condition. -/
theorem of_bool (M : FinTM2) (alphabet : ∀ k, M.Γ k = Bool) : FiniteAlphabet M :=
  of_homogeneous M alphabet

theorem of_equiv (M : FinTM2) {α : Type} [Finite α]
    (alphabet : ∀ k, M.Γ k ≃ α) : FiniteAlphabet M := by
  intro k
  exact Finite.of_equiv α (alphabet k).symm

theorem symbols_finite (M : FinTM2) (finiteAlphabet : FiniteAlphabet M) :
    Finite (Σ k, M.Γ k) := by
  let := M.kFin
  let : ∀ k, Finite (M.Γ k) := finiteAlphabet
  infer_instance

/-- The first two tape groups retain their original alphabets. The sole new
bridge tape uses the second machine's already finite input alphabet. -/
theorem sequential_machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (hfirst : FiniteAlphabet first) (hsecond : FiniteAlphabet second) :
    FiniteAlphabet (MachineSequential.machine first second relabel fallback) := by
  intro tape
  rcases tape with tape | tape | tape
  · exact hfirst tape
  · exact hsecond tape
  · exact input_finite second

/-- Preservation for the machine actually stored in the polynomial-time
composition certificate, with its actual relabeling bridge. -/
theorem compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.compose first second fallback).tm := by
  exact sequential_machine first.tm second.tm
    (fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol))
    (second.inputAlphabet.symm fallback) hfirst hsecond

theorem composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.composeBits first second).tm :=
  compose first second false hfirst hsecond

/-- Counter, temporary, and output tapes of the actual repeat machine all use
the body's finite input alphabet; body tapes retain their original alphabets. -/
theorem repeat_machine (body : FinTM2)
    (input : body.Γ body.k₀ ≃ Bool) (output : body.Γ body.k₁ ≃ Bool)
    (hbody : FiniteAlphabet body) :
    FiniteAlphabet (MachineRepeat.machine body input output) := by
  intro tape
  cases tape with
  | inl tape => exact hbody tape
  | inr _ => exact input_finite body

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

end

end OAI
