import OAI.Analysis.CircleDomains.Sobolev.ComplexCovectorWedge
import OAI.Analysis.CircleDomains.Sobolev.CircleEnergy
import OAI.Analysis.CircleDomains.Topology.CircleChainRule
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

/-! The complex-chart differential norm is exactly the two-coordinate
Euclidean energy used by the finite transfer. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem complexCovector_norm_sq (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = (L 1) ^ 2 + (L Complex.I) ^ 2 := by
  let a := (L 1) ^ 2 + (L Complex.I) ^ 2
  have ha : 0 ≤ a := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hu : ‖L‖ ≤ Real.sqrt a := by
    apply L.opNorm_le_bound (Real.sqrt_nonneg a)
    intro z
    rw [complexCovector_apply, Real.norm_eq_abs]
    have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hsq : (z.re * L 1 + z.im * L Complex.I) ^ 2 ≤ a * ‖z‖ ^ 2 := by
      dsimp only [a]
      rw [hz]
      nlinarith [sq_nonneg (z.re * L Complex.I - z.im * L 1)]
    have hs : (Real.sqrt a * ‖z‖) ^ 2 = a * ‖z‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha]
    nlinarith [sq_abs (z.re * L 1 + z.im * L Complex.I),
      abs_nonneg (z.re * L 1 + z.im * L Complex.I),
      mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg z)]
  have hd := complexCovector_dualVector_norm_le L
  have hdsq : ‖(L 1 : ℂ) + (L Complex.I : ℂ) * Complex.I‖ ^ 2 = a := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    dsimp only [a]
    ring
  have hlo := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hhi := pow_le_pow_left₀ (norm_nonneg L) hu 2
  rw [hdsq] at hlo
  rw [Real.sq_sqrt ha] at hhi
  exact le_antisymm hhi hlo

theorem circleFDeriv_complex_norm_sq
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {u : (ℝ × ℝ) → UnitAddCircle}
    (hu : SmoothCircleOn u D) {z : ℂ} (hz : Complex.equivRealProdCLM z ∈ D) :
    ‖circleFDeriv (u ∘ Complex.equivRealProdCLM) z‖ ^ 2 =
      fieldEnergy (circleGradient u) (fun _ => 1) (Complex.equivRealProdCLM z) := by
  rw [complexCovector_norm_sq, circleFDeriv_comp hD hu Complex.equivRealProdCLM.differentiableAt hz,
    Complex.equivRealProdCLM.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.equivRealProdCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    fieldEnergy, circleGradient, covectorEnergy_identity]

theorem integral_circleFDeriv_complex_norm_sq
    {D A : Set (ℝ × ℝ)} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    {u : (ℝ × ℝ) → UnitAddCircle} (hu : SmoothCircleOn u D) :
    (∫ z in Complex.equivRealProdCLM ⁻¹' A,
      ‖circleFDeriv (u ∘ Complex.equivRealProdCLM) z‖ ^ 2) =
      ∫ x in A, fieldEnergy (circleGradient u) (fun _ => 1) x := by
  calc
    _ = ∫ z in Complex.equivRealProdCLM ⁻¹' A,
        fieldEnergy (circleGradient u) (fun _ => 1) (Complex.equivRealProdCLM z) := by
      apply setIntegral_congr_fun (hA.preimage Complex.equivRealProdCLM.continuous.measurable)
      intro z hz
      exact circleFDeriv_complex_norm_sq hD hu (hAD hz)
    _ = _ := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding _ A

theorem memLp_circleFDeriv_complex
    {D A : Set (ℝ × ℝ)} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    {u : (ℝ × ℝ) → UnitAddCircle} (hu : SmoothCircleOn u D)
    (hi : IntegrableOn (fieldEnergy (circleGradient u) (fun _ => 1)) A) :
    MemLp (circleFDeriv (u ∘ Complex.equivRealProdCLM)) 2
      (volume.restrict (Complex.equivRealProdCLM ⁻¹' A)) := by
  have hmp := Complex.volume_preserving_equiv_real_prod.restrict_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding A
  have hcomp : IntegrableOn (fun z : ℂ => fieldEnergy (circleGradient u) (fun _ => 1)
      (Complex.equivRealProdCLM z)) (Complex.equivRealProdCLM ⁻¹' A) :=
    (hmp.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hsm : SmoothCircleOn (u ∘ Complex.equivRealProdCLM) (Complex.equivRealProdCLM ⁻¹' D) := by
    intro z hz a ha
    exact (hu _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  have hm : AEStronglyMeasurable (circleFDeriv (u ∘ Complex.equivRealProdCLM))
      (volume.restrict (Complex.equivRealProdCLM ⁻¹' A)) := ((contDiffOn_circleFDeriv (hD.preimage Complex.equivRealProdCLM.continuous) hsm).continuousOn.mono
    (preimage_mono hAD)).aestronglyMeasurable (hA.preimage Complex.equivRealProdCLM.continuous.measurable)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply hcomp.congr
  filter_upwards [ae_restrict_mem (hA.preimage Complex.equivRealProdCLM.continuous.measurable)] with z hz
  exact (circleFDeriv_complex_norm_sq hD hu (hAD hz)).symm

end CircleDomainRigidity

end

end OAI
