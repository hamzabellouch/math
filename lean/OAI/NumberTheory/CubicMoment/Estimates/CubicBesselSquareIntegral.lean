import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselSquareHeat

namespace OAI

/-! Absolute Fubini evaluates the square of the cubic Bessel kernel.
Only the fixed order one third and the needed zero Mellin exponent occur. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

private lemma positive_pair_ae :
    ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))),
      p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact ⟨ht,hu⟩

lemma cubicBesselSquareHeat_inner_norm {p : ℝ × ℝ}
    (hp : p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) :
    (∫ x in Ioi (0:ℝ), ‖cubicBesselSquareHeat p x‖)=
      Real.Gamma (4/3)*cubicBesselSumWeight (p.1+p.2) := by
  rw [←cubicBesselSquareHeat_inner hp.1 hp.2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact Real.norm_of_nonneg (cubicBesselSquareHeat_nonneg hp hx)

lemma cubicBesselSquareHeat_integrable :
    Integrable (fun q : (ℝ × ℝ) × ℝ => cubicBesselSquareHeat q.1 q.2)
      (((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))).prod
        (volume.restrict (Ioi 0))) := by
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => cubicBesselSquareHeat q.1 q.2) := by
    unfold cubicBesselSquareHeat cubicBesselHeat
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [positive_pair_ae] with p hp
    exact cubicBesselSquareHeat_inner_integrable hp.1 hp.2
  · apply (cubicBesselSumWeight_integrable.const_mul (Real.Gamma (4/3))).congr
    filter_upwards [positive_pair_ae] with p hp
    exact (cubicBesselSquareHeat_inner_norm hp).symm

lemma cubicBesselKernel_sq_integrable :
    IntegrableOn (fun x : ℝ => (cubicBesselKernel x)^2) (Ioi 0) := by
  apply cubicBesselSquareHeat_integrable.integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (cubicBesselKernel_sq_integral hx).symm

theorem cubicBesselKernel_sq_integral_value :
    (∫ x in Ioi (0:ℝ), (cubicBesselKernel x)^2)=Real.Gamma (4/3)*Real.Gamma (2/3) := by
  calc
    _ = ∫ x in Ioi (0:ℝ), ∫ p : ℝ × ℝ, cubicBesselSquareHeat p x
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact cubicBesselKernel_sq_integral hx
    _ = ∫ p : ℝ × ℝ, (∫ x in Ioi (0:ℝ), cubicBesselSquareHeat p x)
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
      (integral_integral_swap cubicBesselSquareHeat_integrable).symm
    _ = ∫ p : ℝ × ℝ, Real.Gamma (4/3)*cubicBesselSumWeight (p.1+p.2)
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
      apply integral_congr_ae
      filter_upwards [positive_pair_ae] with p hp
      exact cubicBesselSquareHeat_inner hp.1 hp.2
    _ = _ := by rw [integral_const_mul,cubicBesselSumWeight_integral]

end CubicFirstMoment

end

end OAI
