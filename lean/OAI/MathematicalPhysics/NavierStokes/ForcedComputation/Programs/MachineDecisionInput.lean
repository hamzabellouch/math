import OAI.MathematicalPhysics.NavierStokes.Material.Model

namespace OAI

/-! The machine-theoretic published input for the decision corollaries.

A. M. Turing, On computable numbers, with an application to the
Entscheidungsproblem, Proc. London Math. Soc. (2) 42 (1936–1937), 230–265,
Section 8, printed p.248: undecidability of ever printing a designated symbol.
No fluid event, force compiler, or geometric conclusion is assumed.
-/

namespace ForcedComputation

/-- The standard halting undecidability specialization to finite one-tape
machine tables. Correctness is required on every well-formed finite input. -/
def FiniteMachineHaltingUndecidable : Prop :=
  ¬ ∃ d : Alternating.MachineInput → Bool, Computable d ∧
    ∀ I, Alternating.ValidInput I → (d I = true ↔ Alternating.Halts I)

/-- No total algorithm on the finite source descriptions decides the given
observation for all valid compiled inputs. -/
def NoCompiledInputDecider
    (event : (I : Alternating.MachineInput) → Alternating.ValidInput I → Prop) : Prop :=
  ¬ ∃ d : Alternating.MachineInput → Bool, Computable d ∧
    ∀ I hI, d I = true ↔ event I hI

theorem noCompiledInputDecider_of_halting (hT : FiniteMachineHaltingUndecidable)
    {event : (I : Alternating.MachineInput) → Alternating.ValidInput I → Prop}
    (he : ∀ I hI, event I hI ↔ Alternating.Halts I) : NoCompiledInputDecider event := by
  rintro ⟨d, hd, hcorrect⟩
  exact hT ⟨d, hd, fun I hI => (hcorrect I hI).trans (he I hI)⟩

end ForcedComputation

end OAI
