import OAI.MeasureTheory.Falconer.Estimates.WeightedCauchy

namespace OAI

/-! # Spatial Fourier integration followed by sphere Cauchy--Schwarz

This transfers the actual shared-angle integral of a separated inverse term
to positive independent-angle energies, at the squared L1 cost of its
spatial Fourier coefficient.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

variable {d : ℕ}

theorem spatial_shared_integral_sq_le
    (c : Space d → ℂ) (hcm : Measurable c) (hc : Integrable c)
    (U V : Space d × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbU : ∀ z, ‖U z‖ ≤ B) (hbV : ∀ z, ‖V z‖ ≤ C) :
    ‖∫ w : Sphere d, (∫ ξ : Space d, c ξ*(U (ξ,w)*star (V (ξ,w)) ))
      ∂sphereMeasure d‖^2 ≤
    (∫ ξ : Space d, ‖c ξ‖) *
      ∫ ξ : Space d, ‖c ξ‖*((∫ w : Sphere d, ‖U (ξ,w)‖^2 ∂sphereMeasure d)*
        (∫ w : Sphere d, ‖V (ξ,w)‖^2 ∂sphereMeasure d)) := by
  let F : Space d → ℂ := fun ξ => ∫ w : Sphere d, U (ξ,w)*star (V (ξ,w)) ∂sphereMeasure d
  have hm : Measurable (fun z : Space d × Sphere d => U z*star (V z)) :=
    hU.mul (continuous_star.measurable.comp hV)
  have hFm : Measurable F := hm.stronglyMeasurable.integral_prod_right'.measurable
  have hbound : ∀ z, ‖U z*star (V z)‖ ≤ B*C := by
    intro z
    rw [norm_mul,norm_star]
    exact mul_le_mul (hbU z) (hbV z) (norm_nonneg _) hB
  have hFb : ∀ ξ, ‖F ξ‖ ≤ B*C*(sphereMeasure d).real univ := by
    intro ξ
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun w => hbound (ξ,w))
  have hi : Integrable (fun z : Space d × Sphere d => c z.1*(U z*star (V z)))
      (volume.prod (sphereMeasure d)) := by
    apply ((hc.norm.comp_fst (sphereMeasure d)).mul_const (B*C)).mono'
      ((hcm.comp measurable_fst).mul hm).aestronglyMeasurable
    filter_upwards with z
    dsimp only [Pi.mul_apply,Function.comp_apply]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg _)
  have he : (∫ w : Sphere d, (∫ ξ : Space d, c ξ*(U (ξ,w)*star (V (ξ,w))))
      ∂sphereMeasure d) = ∫ ξ : Space d, c ξ*F ξ := by
    simpa only [F,integral_const_mul] using
      (integral_integral_swap (f := fun ξ w => c ξ*(U (ξ,w)*star (V (ξ,w)))) hi).symm
  rw [he]
  have hcs := norm_integral_weighted_sq_le volume c F hcm hc hFm
    (mul_nonneg (mul_nonneg hB hC) (measureReal_nonneg)) hFb
  let G : Space d → ℝ := fun ξ =>
    (∫ w : Sphere d, ‖U (ξ,w)‖^2 ∂sphereMeasure d)*
      (∫ w : Sphere d, ‖V (ξ,w)‖^2 ∂sphereMeasure d)
  have hGm : Measurable G :=
    (hU.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable.mul
      (hV.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => mul_nonneg
    (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hGb : ∀ ξ, G ξ ≤
      (B^2*(sphereMeasure d).real univ)*(C^2*(sphereMeasure d).real univ) := by
    intro ξ
    exact mul_le_mul
      (sphereMoment_le (fun z => U (ξ,z.2)) hB (fun z => hbU (ξ,z.2)) 0)
      (sphereMoment_le (fun z => V (ξ,z.2)) hC (fun z => hbV (ξ,z.2)) 0)
      (integral_nonneg fun _ => sq_nonneg _) (by positivity)
  have hF2 : ∀ ξ, ‖F ξ‖^2 ≤ G ξ := by
    intro ξ
    simpa only [F,G,one_smul] using sphere_shared_integral_sq_le
      (fun w => U (ξ,w)) (fun w => V (ξ,w)) (fun _ => 1)
      (hU.comp (measurable_const.prodMk measurable_id))
      (hV.comp (measurable_const.prodMk measurable_id)) (by simp) hB hC
      (fun w => hbU (ξ,w)) (fun w => hbV (ξ,w))
  have hGi : Integrable (fun ξ => ‖c ξ‖*G ξ) := by
    apply (hc.norm.mul_const ((B^2*(sphereMeasure d).real univ)*
      (C^2*(sphereMeasure d).real univ))).mono' (hcm.norm.mul hGm).aestronglyMeasurable
    filter_upwards with ξ
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (hG0 ξ))]
    exact mul_le_mul_of_nonneg_left (hGb ξ) (norm_nonneg _)
  have hFi : Integrable (fun ξ => ‖c ξ‖*‖F ξ‖^2) := by
    apply hGi.mono' (hcm.norm.mul (hFm.norm.pow_const 2)).aestronglyMeasurable
    filter_upwards with ξ
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hF2 ξ) (norm_nonneg _)
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (integral_mono hFi hGi (fun ξ => mul_le_mul_of_nonneg_left (hF2 ξ) (norm_nonneg _)))
    (integral_nonneg fun _ => norm_nonneg _))

end Falconer

end OAI
