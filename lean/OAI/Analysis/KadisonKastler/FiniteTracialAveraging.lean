import OAI.Analysis.KadisonKastler.FiniteTracialDixmier
import OAI.Analysis.KadisonKastler.SelfAdjointAveraging

namespace OAI

/-! # Finite-factor averaging of arbitrary operators -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

/-- Every operator in the diffuse finite factor admits scalar finite averages. -/
theorem exists_tracial_scalar_average (τ : TracialRepresentation M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (x : Algebra M) (ε : ℝ) (hε : 0 < ε) :
    ∃ (C : FiniteInnerAverage M) (z : ℂ),
      ‖C.apply x.val - z • (1 : H →L[ℂ] H)‖ < ε := by
  apply exists_scalar_average_of_selfAdjoint (M := M) ?_ x ε hε
  intro y hy δ hδ
  let _ : IsStarNormal y := hy.isStarNormal
  exact exists_tracial_normal_scalar_average τ hfactor hdiff y δ hδ

end

end KadisonKastler

end OAI
