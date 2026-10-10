import OAI.NumberTheory.CubicMoment.Estimates.DyadicWeightIntegral

namespace OAI

/-! Transfer an actual positive height majorant to a supported integral.
No regularity of the complex integrand is assumed beyond the majorant. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma normalized_dyadic_integral_majorant (f h : ℝ → ℂ) (g : ℝ → ℝ)
    (hg : Continuous g) {T : ℝ} (hT : 0 < T)
    (hh : ∀ t, ‖h t‖ ≤ 1)
    (hs : ∀ t, t ∉ dyadicHeightSupport T → h t = 0)
    (hfg : ∀ t, ‖f t‖ ≤ g t) :
    ‖(T:ℂ)⁻¹*(∫ t : ℝ, h t*f t)‖ ≤ dyadicHeightMean g T := by
  let S := dyadicHeightSupport T
  have hS : MeasurableSet S := measurableSet_Icc.union measurableSet_Icc
  have hi : Integrable (S.indicator g) :=
    (hg.continuousOn.integrableOn_compact
      (isCompact_Icc.union isCompact_Icc)).integrable_indicator hS
  have hb : ‖∫ t : ℝ, h t*f t‖ ≤ ∫ t : ℝ, S.indicator g t := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards with t
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht,norm_mul]
      exact (mul_le_of_le_one_left (_root_.norm_nonneg _) (hh t)).trans (hfg t)
    · rw [indicator_of_notMem ht,hs t ht,zero_mul,norm_zero]
  have hd : Disjoint (Icc T (2*T)) (Icc (-2*T) (-T)) := by
    apply Set.disjoint_left.mpr
    intro t hp hn
    linarith [hp.1,hn.2]
  rw [integral_indicator hS] at hb
  change ‖∫ t : ℝ, h t*f t‖ ≤ ∫ t in Icc T (2*T) ∪ Icc (-2*T) (-T), g t at hb
  rw [setIntegral_union hd measurableSet_Icc hg.integrableOn_Icc hg.integrableOn_Icc,
    integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by linarith : T ≤ 2*T),
    ←intervalIntegral.integral_of_le (by linarith : -2*T ≤ -T)] at hb
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hT.le]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hT.le)).trans_eq
  dsimp [dyadicHeightMean]
  ring

end CubicFirstMoment

end

end OAI
