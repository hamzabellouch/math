import OAI.Analysis.CircleDomains.Sobolev.InverseOnDerivativeField
import OAI.Analysis.CircleDomains.Sobolev.WeightedDifferentiableCurve
import OAI.Analysis.CircleDomains.Topology.VerticalLevelCurve

namespace OAI

/-! Weighted arclength on vertical fibers of the inverse of a regular measurable piece. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma inverse_piece_vertical_derivative_norm (B : ℂ →L[ℝ] ℂ) :
    ‖B.comp (ContinuousLinearMap.toSpanSingleton ℝ Complex.I)‖ = ‖B Complex.I‖ := by
  have h := norm_real_clm_apply (B.comp (ContinuousLinearMap.toSpanSingleton ℝ Complex.I)) 1
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, abs_one, mul_one] using h.symm

lemma weighted_inverse_piece_vertical_curve {F : ℂ → ℂ} {S : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F))
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    {T : Set ℂ} (hT : MeasurableSet T) (hb : IsBounded T) (hTS : T ⊆ F '' S)
    (t : ℝ) {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ z in ((invFunOn F S) ∘ coareaVerticalLine t) '' ((coareaVerticalLine t) ⁻¹' T), q z ∂μH[1]) =
    ∫⁻ s in (coareaVerticalLine t) ⁻¹' T,
      q (invFunOn F S (coareaVerticalLine t s)) *
      ENNReal.ofReal ‖(fderiv ℝ F (invFunOn F S (coareaVerticalLine t s))).inverse Complex.I‖ := by
  let J := (coareaVerticalLine t) ⁻¹' T
  let D : ℝ → ℝ →L[ℝ] ℂ := fun s =>
    (fderiv ℝ F (invFunOn F S (coareaVerticalLine t s))).inverse.comp
      (ContinuousLinearMap.toSpanSingleton ℝ Complex.I)
  have hJ : MeasurableSet J := hT.preimage (coareaVerticalLine_contDiff t).continuous.measurable
  have hder : ∀ s ∈ J, HasFDerivWithinAt ((invFunOn F S) ∘ coareaVerticalLine t) (D s) J s := by
    intro s hs
    exact ((inverseOn_derivative_field hF hd hi (hTS hs)).mono hTS).comp s
      (coareaVerticalLine_hasFDerivAt t s).hasFDerivWithinAt (fun _ hx => hx)
  have hinj : InjOn ((invFunOn F S) ∘ coareaVerticalLine t) J := by
    intro a ha b hb he
    exact coareaVerticalLine_injective t (inverseOn_injOn (hTS ha) (hTS hb) he)
  have hnorm (s : ℝ) : ‖D s‖ =
      ‖(fderiv ℝ F (invFunOn F S (coareaVerticalLine t s))).inverse Complex.I‖ :=
    inverse_piece_vertical_derivative_norm _
  have hBm := (ContinuousLinearMap.measurable_apply Complex.I).comp
    (measurable_inversePieceDifferential hF hT hTS)
  have hm : AEMeasurable (fun s => ENNReal.ofReal ‖D s‖) (volume.restrict J) := by
    apply (((hBm.comp (coareaVerticalLine_contDiff t).continuous.measurable).norm.ennreal_ofReal).aemeasurable).congr
    filter_upwards [ae_restrict_mem hJ] with s hs
    dsimp only [Function.comp_def]
    rw [hnorm, inverseOnPiece_eq hs]
  rw [weighted_differentiable_curve_length hJ (vertical_slice_bounded hb t) hinj hder hm hq]
  apply setLIntegral_congr_fun hJ
  intro s _
  dsimp only [Function.comp_def]
  rw [hnorm]

end CircleDomainRigidity

end

end OAI
