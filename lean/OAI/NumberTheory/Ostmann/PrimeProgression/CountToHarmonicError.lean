import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicMain

namespace OAI

open scoped BigOperators
open Set MeasureTheory
namespace Ostmann.Arithmetic.PrimeProgression

lemma abs_inv_mul_le_of_abs_le_mul {x δ r : ℝ} (hx : 0 < x) (hr : |r| ≤ δ * x) :
    |x⁻¹ * r| ≤ δ := by
  rw [abs_mul, abs_of_pos (inv_pos.mpr hx)]
  calc
    x⁻¹ * |r| ≤ x⁻¹ * (δ * x) := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hx.le)
    _ = δ := by field_simp

theorem reciprocal_count_error_bound (c : ℕ → ℝ) (F D : ℝ → ℝ) {A B δ : ℝ}
    (hA : 0 < A) (hAB : A ≤ B)
    (hF : ∀ t ∈ Icc A B, HasDerivAt F (D t) t) (hD : ContinuousOn D (Icc A B))
    (herror : ∀ t ∈ Icc A B, |cumulativeSum c t - F t| ≤ δ * t) :
    |(∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, (n : ℝ)⁻¹ * c n) -
        (∫ t in A..B, t⁻¹ * D t)| ≤ (2 + Real.log B - Real.log A) * δ := by
  have hB := hA.trans_le hAB
  have hiC : IntervalIntegrable (fun t => (t ^ 2)⁻¹ * cumulativeSum c t) volume A B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr
      (cumulativeSum_inv_sq_integrable c hA)
  have hiF : IntervalIntegrable (fun t => (t ^ 2)⁻¹ * F t) volume A B :=
    ((continuousOn_inv_sq hA).mul (continuousOn_of_hasDerivAt_Icc F D hF)).intervalIntegrable_of_Icc hAB
  have hiK : IntervalIntegrable (fun t => (t ^ 2)⁻¹ * (cumulativeSum c t - F t)) volume A B := by
    simp_rw [mul_sub]
    exact hiC.sub hiF
  have hiInv : IntervalIntegrable (fun t : ℝ => δ * t⁻¹) volume A B :=
    ((continuousOn_inv_Icc hA).const_mul δ).intervalIntegrable_of_Icc hAB
  have hpoint (t : ℝ) (ht : t ∈ Icc A B) :
      |(t ^ 2)⁻¹ * (cumulativeSum c t - F t)| ≤ δ * t⁻¹ := by
    have htpos : 0 < t := hA.trans_le ht.1
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
    calc
      (t ^ 2)⁻¹ * |cumulativeSum c t - F t| ≤ (t ^ 2)⁻¹ * (δ * t) :=
        mul_le_mul_of_nonneg_left (herror t ht) (inv_nonneg.mpr (sq_nonneg t))
      _ = δ * t⁻¹ := by field_simp
  have hIntegral : |∫ t in A..B, (t ^ 2)⁻¹ * (cumulativeSum c t - F t)| ≤
      δ * (Real.log B - Real.log A) := by
    calc
      _ ≤ ∫ t in A..B, |(t ^ 2)⁻¹ * (cumulativeSum c t - F t)| :=
        intervalIntegral.abs_integral_le_integral_abs hAB
      _ ≤ ∫ t in A..B, δ * t⁻¹ :=
        intervalIntegral.integral_mono_on hAB hiK.abs hiInv hpoint
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hA hB,
          Real.log_div hB.ne' hA.ne']
  have hEA := abs_inv_mul_le_of_abs_le_mul hA (herror A ⟨le_rfl, hAB⟩)
  have hEB := abs_inv_mul_le_of_abs_le_mul hB (herror B ⟨hAB, le_rfl⟩)
  rw [reciprocal_count_error_identity c F D hA hAB hF hD]
  calc
    _ ≤ |B⁻¹ * (cumulativeSum c B - F B)| + |A⁻¹ * (cumulativeSum c A - F A)| +
        |∫ t in A..B, (t ^ 2)⁻¹ * (cumulativeSum c t - F t)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ δ + δ + δ * (Real.log B - Real.log A) :=
      add_le_add (add_le_add hEB hEA) hIntegral
    _ = _ := by ring

end Ostmann.Arithmetic.PrimeProgression

end OAI
