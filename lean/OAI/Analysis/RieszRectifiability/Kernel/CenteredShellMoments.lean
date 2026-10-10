import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.InnerEnergyRestriction

namespace OAI

/-!
Second-moment and mass bounds control moments after subtracting a constant. Applying this
estimate to dyadic annuli yields centered shell bounds at the prescribed geometric scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem centered_moment_from_scale {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (u : X → ℝ) (hu : MemLp u 2 ν)
    (M D δ A b : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hmass : ν.real univ ≤ M) (hsecond : (∫ x, u x ^ 2 ∂ν) ≤ M * A ^ 2)
    (hb : b ^ 2 ≤ D * δ ^ 2) (hscale : δ ^ 2 ≤ A ^ 2) :
    (∫ x, (u x - b) ^ 2 ∂ν) ≤ (2 * (1 + D) * M) * A ^ 2 := by
  have hbA := hb.trans (mul_le_mul_of_nonneg_left hscale hD)
  apply (centered_second_moment_le ν u hu b).trans
  calc
    _ ≤ 2 * (M * A ^ 2) + 2 * M * (D * A ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hsecond (by norm_num))
        (mul_le_mul (mul_le_mul_of_nonneg_left hmass (by norm_num)) hbA (sq_nonneg _) (by positivity))
    _ = _ := by ring

theorem centered_shell_second_moment {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (u : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (a : Ambient d) (R : ℝ) (hR : 1 ≤ R) (k : ℕ)
    (δ β D b : ℝ) (hδ : 0 ≤ δ) (hβ : 1 ≤ β) (hD : 0 ≤ D)
    (hb : b ^ 2 ≤ D * δ ^ 2)
    (hsecond : (∫ y in dyadicAnnulus a R k, u y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * β ^ k) ^ 2) :
    (∫ y in dyadicAnnulus a R k, (u y - b) ^ 2 ∂μ) ≤
      ((2 * (1 + D) * B) * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * β ^ k) ^ 2 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let ν := μ.restrict (dyadicAnnulus a R k)
  have : IsFiniteMeasure ν := ⟨by
    simpa only [ν, Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hRpos k⟩
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hmass : ν.real univ ≤ B * (R * 2 ^ k) ^ m := by
    have hmass' : μ.real (dyadicAnnulus a R k) ≤ C * (R * 2 ^ (k + 1)) ^ m :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
        ((measure_mono (dyadicAnnulus_subset_ball a R k)).trans (hg.2 a _ (by positivity)))
    have heq : C * (R * (2 : ℝ) ^ (k + 1)) ^ m = (C * 2 ^ m) * (R * 2 ^ k) ^ m := by
      rw [pow_succ, show R * ((2 : ℝ) ^ k * 2) = (R * 2 ^ k) * 2 by ring, mul_pow]
      ring
    simpa only [ν, Measure.real, Measure.restrict_apply_univ] using!
      hmass'.trans (heq ▸ mul_le_mul_of_nonneg_right hCB (by positivity))
  have hscale : δ ≤ δ * (R * 2 ^ k) * β ^ k := by
    have ht : 1 ≤ R * (2 : ℝ) ^ k := hR.trans (by
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hRpos.le)
    calc
      δ ≤ δ * (R * 2 ^ k) := by simpa only [mul_one] using! mul_le_mul_of_nonneg_left ht hδ
      _ ≤ _ := by simpa only [mul_one] using!
        mul_le_mul_of_nonneg_left (one_le_pow₀ hβ) (by positivity : 0 ≤ δ * (R * 2 ^ k))
  have h := centered_moment_from_scale ν u (lipschitz_height_memLp_on_annulus m C μ hg u K hu a R hRpos k)
    (B * (R * 2 ^ k) ^ m) D δ (δ * (R * 2 ^ k) * β ^ k) b (by positivity) hD hmass hsecond hb
    (pow_le_pow_left₀ hδ hscale 2)
  convert! h using 1
  ring

theorem cutoffMean_sq_le_amplitude {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (u χ : X → ℝ)
    (hu : Measurable u) (hχ : Measurable χ) (huL2 : MemLp u 2 ν)
    (hχbound : ∀ x, |χ x| ≤ 1) (c M δ : ℝ) (hc : 0 < c)
    (hcutmass : c ≤ ∫ x, χ x ^ 2 ∂ν)
    (hsecond : (∫ x, u x ^ 2 ∂ν) ≤ M * δ ^ 2) :
    cutoffMean ν u χ ^ 2 ≤ (M / c) * δ ^ 2 := by
  apply (cutoffMean_sq_bound ν u χ hu hχ huL2 hχbound c hc hcutmass).trans
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using!
    div_le_div_of_nonneg_right hsecond hc.le

theorem cutoffMean_abs_le_uniform {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (u χ : X → ℝ)
    (hu : Measurable u) (hχ : Measurable χ) (huL2 : MemLp u 2 ν)
    (hχbound : ∀ x, |χ x| ≤ 1) (c M δ : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hcutmass : c ≤ ∫ x, χ x ^ 2 ∂ν)
    (hsecond : (∫ x, u x ^ 2 ∂ν) ≤ M * δ ^ 2) :
    |cutoffMean ν u χ| ≤ Real.sqrt (M / c) := by
  have hs := cutoffMean_sq_le_amplitude ν u χ hu hχ huL2 hχbound c M δ hc hcutmass hsecond
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith
  have hsq : cutoffMean ν u χ ^ 2 ≤ M / c :=
    hs.trans (by simpa only [mul_one] using! mul_le_mul_of_nonneg_left hδsq (by positivity : 0 ≤ M / c))
  have hr := Real.sq_sqrt (show 0 ≤ M / c by positivity)
  exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by simpa only [sq_abs, hr] using! hsq)

end

end RieszRectifiability

end OAI
