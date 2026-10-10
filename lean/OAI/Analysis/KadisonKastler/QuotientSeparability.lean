import OAI.Analysis.KadisonKastler.TraceSeparability
import OAI.Analysis.KadisonKastler.TraceSeparableAdjoin
import OAI.Analysis.KadisonKastler.UltrapowerExpectation

namespace OAI

/-! # Separability of the constant algebra in a trace quotient -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
variable {C : Type*} [CStarAlgebra C] {τ : FaithfulTracialState (Algebra M)}
variable {σ : FaithfulTracialState C} {ω : Ultrafilter ℕ}

/-- A separably acting finite-vector trace supplies the separability
premise for the constant subalgebra of the represented ultrapower. -/
theorem TraceQuotientMap.constant_traceSeparable (Q : TraceQuotientMap τ σ ω)
    (hτ : FiniteVectorTrace τ) :
    TraceSeparable σ (Q.constant.range : Set C) := by
  have h := (hτ.traceSeparable (Set.univ : Set (Algebra M))).map
    (Q.constant (M := M)) (Q.trace_constant (M := M))
  change TraceSeparable σ (Set.range (Q.constant (M := M)))
  simpa only [Set.image_univ] using h

end

end KadisonKastler

end OAI
