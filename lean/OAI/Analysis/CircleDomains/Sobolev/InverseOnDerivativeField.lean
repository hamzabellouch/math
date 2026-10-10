import OAI.Analysis.CircleDomains.Probability.MeasurablePieceInverse

namespace OAI

/-! The actual derivative field of an inverse on a regular measurable piece. -/
open Set Function MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma inverseOn_derivative_field {F : ℂ → ℂ} {S : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F))
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    {y : ℂ} (hy : y ∈ F '' S) :
    HasFDerivWithinAt (invFunOn F S) (fderiv ℝ F (invFunOn F S y)).inverse (F '' S) y := by
  have hx : invFunOn F S y ∈ S := invFunOn_mem hy
  obtain ⟨A, hA⟩ := hi _ hx
  rw [← hA, ContinuousLinearMap.inverse_equiv]
  apply inverseOn_hasFDerivWithinAt hF hy A
  rw [hA]
  exact (hd _ hx).hasFDerivAt.hasFDerivWithinAt

end CircleDomainRigidity

end

end OAI
