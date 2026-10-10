import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CutoffTestMoments

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

def cutoffMean (ν : Measure X) (u χ : X → ℝ) : ℝ :=
  (∫ x, χ x ^ 2 * u x ∂ν) / (∫ x, χ x ^ 2 ∂ν)

theorem cutoffMean_integral_zero (ν : Measure X) [IsFiniteMeasure ν]
    (u χ : X → ℝ) (hu : Measurable u) (hχ : Measurable χ)
    (huL2 : MemLp u 2 ν) (hbound : ∀ x, |χ x| ≤ 1)
    (hdenom : (∫ x, χ x ^ 2 ∂ν) ≠ 0) :
    (∫ x, χ x ^ 2 * (u x - cutoffMean ν u χ) ∂ν) = 0 := by
  have htest := (squared_cutoff_test_memLp ν u χ hu hχ huL2 hbound).integrable (by norm_num)
  have hχL2 : MemLp χ 2 ν := MemLp.of_bound hχ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hbound x)
  simp_rw [mul_sub]
  rw [integral_sub htest (hχL2.integrable_sq.mul_const _), integral_mul_const]
  unfold cutoffMean
  field_simp
  ring

theorem cutoffMean_sq_bound (ν : Measure X) [IsFiniteMeasure ν]
    (u χ : X → ℝ) (hu : Measurable u) (hχ : Measurable χ)
    (huL2 : MemLp u 2 ν) (hbound : ∀ x, |χ x| ≤ 1)
    (c : ℝ) (hc : 0 < c) (hmass : c ≤ ∫ x, χ x ^ 2 ∂ν) :
    cutoffMean ν u χ ^ 2 ≤ (∫ x, u x ^ 2 ∂ν) / c := by
  have hχL2 : MemLp χ 2 ν := MemLp.of_bound hχ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hbound x)
  have hχuL2 := bounded_multiplier_memLp ν u χ hu hχ huL2 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hbound x)
  have he : (∫ x, (χ x * u x) ^ 2 ∂ν) ≤ ∫ x, u x ^ 2 ∂ν := by
    apply integral_mono hχuL2.integrable_sq huL2.integrable_sq
    intro x
    change (χ x * u x) ^ 2 ≤ u x ^ 2
    rw [mul_pow]
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right (cutoff_square_le_one χ hbound x) (sq_nonneg (u x))
  have hcs := integral_mul_cauchy_schwarz_sq ν (fun x => χ x * u x) χ hχuL2 hχL2
  have hpoint : (fun x => (χ x * u x) * χ x) = fun x => χ x ^ 2 * u x := by
    funext x
    ring
  rw [hpoint] at hcs
  have hd : 0 < ∫ x, χ x ^ 2 ∂ν := hc.trans_le hmass
  have hnum : (∫ x, χ x ^ 2 * u x ∂ν) ^ 2 ≤
      (∫ x, u x ^ 2 ∂ν) * (∫ x, χ x ^ 2 ∂ν) :=
    hcs.trans (mul_le_mul_of_nonneg_right he hd.le)
  calc
    cutoffMean ν u χ ^ 2 ≤ (∫ x, u x ^ 2 ∂ν) / (∫ x, χ x ^ 2 ∂ν) := by
      unfold cutoffMean
      rw [div_pow]
      apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
      convert! hnum using 1
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (integral_nonneg fun x => sq_nonneg (u x)) hc hmass

theorem centered_second_moment_le (ν : Measure X) [IsFiniteMeasure ν]
    (u : X → ℝ) (huL2 : MemLp u 2 ν) (b : ℝ) :
    (∫ x, (u x - b) ^ 2 ∂ν) ≤ 2 * (∫ x, u x ^ 2 ∂ν) + 2 * ν.real univ * b ^ 2 := by
  calc
    _ ≤ ∫ x, 2 * u x ^ 2 + 2 * b ^ 2 ∂ν := by
      apply integral_mono ((huL2.sub (memLp_const b)).integrable_sq)
        ((huL2.integrable_sq.const_mul 2).add (integrable_const _))
      intro x
      change (u x - b) ^ 2 ≤ 2 * u x ^ 2 + 2 * b ^ 2
      nlinarith [sq_nonneg (u x + b)]
    _ = _ := by
      rw [integral_add (huL2.integrable_sq.const_mul 2) (integrable_const _),
        integral_const_mul, integral_const]
      simp only [smul_eq_mul]
      ring

theorem cutoff_centered_second_moment_bound (ν : Measure X) [IsFiniteMeasure ν]
    (u χ : X → ℝ) (hu : Measurable u) (hχ : Measurable χ)
    (huL2 : MemLp u 2 ν) (hbound : ∀ x, |χ x| ≤ 1)
    (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) (hmass : ν.real univ ≤ M)
    (hcutmass : c ≤ ∫ x, χ x ^ 2 ∂ν) :
    (∫ x, (u x - cutoffMean ν u χ) ^ 2 ∂ν) ≤
      (2 + 2 * M / c) * (∫ x, u x ^ 2 ∂ν) := by
  have hb := cutoffMean_sq_bound ν u χ hu hχ huL2 hbound c hc hcutmass
  apply (centered_second_moment_le ν u huL2 (cutoffMean ν u χ)).trans
  calc
    _ ≤ 2 * (∫ x, u x ^ 2 ∂ν) + 2 * M * ((∫ x, u x ^ 2 ∂ν) / c) := by
      exact add_le_add le_rfl (mul_le_mul
        (mul_le_mul_of_nonneg_left hmass (by norm_num)) hb (sq_nonneg _) (by positivity))
    _ = _ := by ring

theorem cutoff_mass_lower_of_one_on (ν : Measure X) [IsFiniteMeasure ν]
    (χ : X → ℝ) (hχ : Measurable χ) (hbound : ∀ x, |χ x| ≤ 1)
    (s : Set X) (hs : MeasurableSet s) (hone : ∀ x ∈ s, χ x = 1) :
    ν.real s ≤ ∫ x, χ x ^ 2 ∂ν := by
  have hχL2 : MemLp χ 2 ν := MemLp.of_bound hχ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hbound x)
  calc
    ν.real s = ∫ x in s, χ x ^ 2 ∂ν := by
      calc
        ν.real s = ∫ _ in s, (1 : ℝ) ∂ν := by simp
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hs] with x hx
          rw [hone x hx, one_pow]
    _ ≤ _ := setIntegral_le_integral hχL2.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg (χ x))

end

end RieszRectifiability

end OAI
