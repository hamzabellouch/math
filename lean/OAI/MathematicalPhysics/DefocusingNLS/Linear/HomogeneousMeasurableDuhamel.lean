import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalIntegrable
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDuhamel

namespace OAI

/-! # The free Duhamel integral for measurable, integrable forcing -/

open MeasureTheory Set

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

theorem stronglyMeasurable_homogeneousDuhamelIntegrand (a b k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (r : ℝ → HomogeneousY a k) (hr : StronglyMeasurable r) :
    StronglyMeasurable (fun s => homogeneousFreeOperator a b k (t - s) ha ha1 hk (r s)) :=
  (continuous_homogeneousFreeOperator_uncurry a b k ha ha1 hk).comp_stronglyMeasurable
    ((continuous_const.sub continuous_id).stronglyMeasurable.prodMk hr)

theorem integrableOn_homogeneousDuhamelIntegrand (a b k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (r : ℝ → HomogeneousY a k) (hr : StronglyMeasurable r)
    (hir : IntegrableOn r (Icc 0 t)) :
    IntegrableOn (fun s => homogeneousFreeOperator a b k (t - s) ha ha1 hk (r s)) (Icc 0 t) := by
  apply hir.norm.mono'
    (stronglyMeasurable_homogeneousDuhamelIntegrand a b k t ha ha1 hk r hr).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2
  have he : Real.exp (-a * (t - s) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  exact (homogeneousFreeOperator_forward_bound a b k (t - s) ha ha1 hk hts (r s)).trans
    (mul_le_of_le_one_left (norm_nonneg _) he)

theorem homogeneousDuhamel_measurable_norm_le (a b k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ht : 0 ≤ t)
    (r : ℝ → HomogeneousY a k) (hr : IntegrableOn r (Icc 0 t)) :
    ‖homogeneousDuhamel a b k ha ha1 hk t r‖ ≤ ∫ s in Icc 0 t, ‖r s‖ := by
  rw [homogeneousDuhamel, intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
  apply norm_integral_le_of_norm_le hr.norm
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2
  have he : Real.exp (-a * (t - s) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  exact (homogeneousFreeOperator_forward_bound a b k (t - s) ha ha1 hk hts (r s)).trans
    (mul_le_of_le_one_left (norm_nonneg _) he)

end DefocusingNLS

end OAI
