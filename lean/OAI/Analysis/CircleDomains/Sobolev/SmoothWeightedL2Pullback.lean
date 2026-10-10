import OAI.Analysis.CircleDomains.Reflection.SmoothBeltramiCancellation
import OAI.Geometry.Cannon.Beltrami.ContinuousMemLpRestrict

namespace OAI

/-! The weighted L2 pullback used by Beltrami cancellation. The Jacobian
change of variables absorbs the derivative of the smooth comparison. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma differentiable_homeomorph_quasiMeasurePreserving (P : ℂ ≃ₜ ℂ)
    (hPi : Differentiable ℝ (P.symm : ℂ → ℂ)) :
    Measure.QuasiMeasurePreserving P volume volume := by
  refine ⟨P.continuous.measurable,Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hs0
  rw [Measure.map_apply P.continuous.measurable hs]
  have heq : P.symm '' s=P ⁻¹' s := by simpa using P.symm.image_eq_preimage_symm s
  rw [←heq]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hPi.differentiableOn hs0

lemma smooth_weighted_L2_pullback (P : ℂ ≃ₜ ℂ)
    (hP : ContDiff ℝ ∞ (P : ℂ → ℂ)) (hPi : ContDiff ℝ ∞ (P.symm : ℂ → ℂ))
    {K : ℝ} (_hK : 0≤K)
    (hD : ∀z,‖fderiv ℝ (P : ℂ → ℂ) z‖^2≤K*|(fderiv ℝ (P : ℂ → ℂ) z).det|)
    {e : ℂ → ℂ} (he : MemLp e 2 volume) {A : Set ℂ} (hA : MeasurableSet A) :
    MemLp (fun z => e (P z)*star (partialZ P z)) 2 (volume.restrict A) ∧
      (∫z in A,‖e (P z)*star (partialZ P z)‖^2)≤K*(∫z in P '' A,‖e z‖^2) := by
  let q := fun z => e (P z)*star (partialZ P z)
  have hm : AEStronglyMeasurable q volume :=
    (he.aestronglyMeasurable.comp_quasiMeasurePreserving
      (differentiable_homeomorph_quasiMeasurePreserving P (hPi.differentiable (by simp)))).mul
      ((Complex.continuous_conj.comp (contDiff_partials hP).1.continuous).aestronglyMeasurable)
  have hf (z : ℂ) (_hz : z∈A) : HasFDerivWithinAt (P : ℂ → ℂ)
      (fderiv ℝ (P : ℂ → ℂ) z) A z :=
    (hP.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt
  have hei : IntegrableOn (fun z => ‖e z‖^2) (P '' A) :=
    (he.integrable_norm_pow (p := 2) (by norm_num)).integrableOn
  have hw : IntegrableOn (fun z => |(fderiv ℝ (P : ℂ → ℂ) z).det| *‖e (P z)‖^2) A := by
    simpa only [smul_eq_mul] using
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hA hf
        P.injective.injOn (fun z => ‖e z‖^2)).mp hei
  have hb (z : ℂ) : ‖q z‖^2≤K*(|(fderiv ℝ (P : ℂ → ℂ) z).det| *‖e (P z)‖^2) := by
    have hz : ‖partialZ P z‖^2≤K*|(fderiv ℝ (P : ℂ → ℂ) z).det| :=
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (partialZ_norm_le P z)).trans (hD z)
    dsimp [q]
    rw [norm_mul,Complex.norm_conj,mul_pow]
    calc
      _ ≤ ‖e (P z)‖^2*(K*|(fderiv ℝ (P : ℂ → ℂ) z).det|) :=
        mul_le_mul_of_nonneg_left hz (sq_nonneg _)
      _ = _ := by ring
  have hqi : IntegrableOn (fun z => ‖q z‖^2) A := by
    apply (hw.const_mul K).mono' (hm.restrict.norm.pow 2)
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hb z
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.restrict).mpr hqi,?_⟩
  calc
    _ ≤ ∫z in A,K*(|(fderiv ℝ (P : ℂ → ℂ) z).det| *‖e (P z)‖^2) :=
      integral_mono_ae hqi (hw.const_mul K) (.of_forall hb)
    _ = K*(∫z in P '' A,‖e z‖^2) := by
      rw [integral_const_mul]
      congr 1
      symm
      simpa only [smul_eq_mul] using
        integral_image_eq_integral_abs_det_fderiv_smul volume hA hf P.injective.injOn (fun z => ‖e z‖^2)

end CircleDomainRigidity

end

end OAI
