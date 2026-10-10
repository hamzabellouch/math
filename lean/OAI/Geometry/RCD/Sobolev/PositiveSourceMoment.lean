import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-!
# The moment estimate used for positive Poisson sources

A weak power-tail bound of exponent `d` gives every smaller positive
moment. In the Poisson argument the tail follows by testing with a
truncation and applying the Dirichlet Sobolev inequality. The constants
below do not depend on an upper bound for the solution.
-/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

private theorem lintegral_small_rpow {q : ℝ} (hq : 0 < q) :
    (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (q - 1))) = ENNReal.ofReal q⁻¹ := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (q - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have he : (∫ t : ℝ in Ioc 0 1, t ^ (q - 1)) = q⁻¹ := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_rpow (Or.inl (by linarith : -1 < q - 1))]
    simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hq.ne', sub_zero, one_div]
  rw [← he]
  symm
  apply ofReal_integral_eq_lintegral_ofReal hi.1
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact Real.rpow_nonneg ht.1.le _

private theorem lintegral_large_rpow {q d : ℝ} (hqd : q < d) :
    (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (q - 1 - d))) =
      ENNReal.ofReal (d - q)⁻¹ := by
  have hexp : q - 1 - d < -1 := by linarith
  have hi := integrableOn_Ioi_rpow_of_lt hexp (by norm_num : (0 : ℝ) < 1)
  have he : (∫ t : ℝ in Ioi 1, t ^ (q - 1 - d)) = (d - q)⁻¹ := by
    rw [integral_Ioi_rpow_of_lt hexp (by norm_num : (0 : ℝ) < 1), Real.one_rpow]
    rw [show q - 1 - d + 1 = -(d - q) by ring]
    simp only [div_neg, neg_div, neg_neg, one_div]
  rw [← he]
  symm
  apply ofReal_integral_eq_lintegral_ofReal hi
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact Real.rpow_nonneg (le_of_lt (zero_lt_one.trans ht)) _

/-- A tail bound at levels at least one gives an explicit smaller-moment
bound; low levels cost only the total measure. -/
theorem moment_lintegral_le_of_power_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {H : X → ℝ}
    (hH : AEMeasurable H μ) (hH0 : 0 ≤ᵐ[μ] H)
    {q d C : ℝ} (hq : 0 < q) (hqd : q < d) (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 1 ≤ t → μ {x | t ≤ H x} ≤ ENNReal.ofReal (C * t ^ (-d))) :
    (∫⁻ x, ENNReal.ofReal (H x ^ q) ∂μ) ≤
      ENNReal.ofReal q *
        (μ univ * ENNReal.ofReal q⁻¹ + ENNReal.ofReal C * ENNReal.ofReal (d - q)⁻¹) := by
  rw [lintegral_rpow_eq_lintegral_meas_le_mul μ hH0 hH hq]
  gcongr 1
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
    lintegral_union measurableSet_Ioi (disjoint_left.mpr (by
      intro t ht ht'
      exact (not_lt_of_ge ht.2) ht'))]
  apply add_le_add
  · calc
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, μ univ * ENNReal.ofReal (t ^ (q - 1)) :=
        lintegral_mono fun t => mul_le_mul' (measure_mono (subset_univ _)) le_rfl
      _ = _ := by
        rw [lintegral_const_mul' _ _ (measure_ne_top _ _), lintegral_small_rpow hq]
  · calc
      _ ≤ ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal C * ENNReal.ofReal (t ^ (q - 1 - d)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := zero_lt_one.trans ht
        calc
          μ {x | t ≤ H x} * ENNReal.ofReal (t ^ (q - 1)) ≤
              ENNReal.ofReal (C * t ^ (-d)) * ENNReal.ofReal (t ^ (q - 1)) :=
            mul_le_mul' (htail t ht.le) le_rfl
          _ = ENNReal.ofReal C * ENNReal.ofReal (t ^ (q - 1 - d)) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg ht0.le _)),
              ← ENNReal.ofReal_mul hC]
            congr 1
            rw [mul_assoc, ← Real.rpow_add ht0]
            congr 2
            ring
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_large_rpow hqd]

/-- The tail estimate also supplies genuine integrability of the moment. -/
theorem integrable_rpow_of_power_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {H : X → ℝ}
    (hH : AEMeasurable H μ) (hH0 : 0 ≤ᵐ[μ] H)
    {q d C : ℝ} (hq : 0 < q) (hqd : q < d) (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 1 ≤ t → μ {x | t ≤ H x} ≤ ENNReal.ofReal (C * t ^ (-d))) :
    Integrable (fun x => H x ^ q) μ := by
  refine ⟨(hH.pow_const q).aestronglyMeasurable, ?_⟩
  have hb := moment_lintegral_le_of_power_tail μ hH hH0 hq hqd hC htail
  have hf : (∫⁻ x, ENNReal.ofReal (H x ^ q) ∂μ) < ∞ :=
    lt_of_le_of_lt hb (by finiteness)
  change (∫⁻ x, ‖H x ^ q‖ₑ ∂μ) < ∞
  convert hf using 1
  apply lintegral_congr_ae
  filter_upwards [hH0] with x hx
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg hx q)]

/-- A real-valued form of the moment bound for subsequent energy estimates. -/
theorem integral_rpow_le_of_power_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {H : X → ℝ}
    (hH : AEMeasurable H μ) (hH0 : 0 ≤ᵐ[μ] H)
    {q d C : ℝ} (hq : 0 < q) (hqd : q < d) (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 1 ≤ t → μ {x | t ≤ H x} ≤ ENNReal.ofReal (C * t ^ (-d))) :
    (∫ x, H x ^ q ∂μ) ≤ q * (μ.real univ * q⁻¹ + C * (d - q)⁻¹) := by
  have hb := moment_lintegral_le_of_power_tail μ hH hH0 hq hqd hC htail
  have hi := integrable_rpow_of_power_tail μ hH hH0 hq hqd hC htail
  have hn : ∀ᵐ x ∂μ, 0 ≤ H x ^ q := hH0.mono fun x hx => Real.rpow_nonneg hx q
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at hb
  have ht := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul] at ht
  simpa only [ENNReal.toReal_ofReal hq.le,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hq.le), ENNReal.toReal_ofReal hC,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (sub_pos.mpr hqd).le),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hn), Measure.real] using ht

end RegularPointCoordinates

end

end OAI
