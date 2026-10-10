import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstFrequencyCutoff

namespace OAI

/-! # The first-frequency tail after the original Gauss normalization -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap FourierTransform

private theorem tail_denominator {Y J C : ℝ} (hY : 0 < Y) (hJ : 1 ≤ J)
    (hC : 0 ≤ C) (K A : ℕ) (hcut : J ≤ Y * ((K : ℝ) + 1)) :
    C / (Y ^ (A + 2) * ((K : ℝ) + 1) ^ A) ≤ C / (Y ^ 2 * J ^ A) := by
  apply div_le_div_of_nonneg_left hC (by positivity)
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ J) hcut A
  have he : Y ^ (A + 2) * ((K : ℝ) + 1) ^ A =
      Y ^ 2 * (Y * ((K : ℝ) + 1)) ^ A := by
    rw [pow_add, mul_pow]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hp (by positivity)

theorem quadratic_first_tail_normalized (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M J : ℝ, 0 < M → 1 ≤ J →
      ∀ e q K : ℕ, 0 < e → 1 < q →
      J ≤ (M / ((e : ℝ) * q)) * ((K : ℝ) + 1) →
      ‖(((M / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        ((∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
          𝓕 ψ ((h : ℝ) * M / ((e : ℝ) * q))) -
          quadraticFirstFiniteFrequency ψ M e q K))‖ ≤
        C * ((e : ℝ) * q * Real.sqrt q / M) / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_first_frequency_cutoff ψ A
  refine ⟨C, hC, ?_⟩
  intro M J hM hJ e q K he hq hcut
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hqR
  have hS : 0 < M / ((e : ℝ) * Real.sqrt q) := by positivity
  have hY : 0 < M / ((e : ℝ) * q) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  calc
    _ ≤ (M / ((e : ℝ) * Real.sqrt q)) *
        (C / ((M / ((e : ℝ) * q)) ^ (A + 2) * ((K : ℝ) + 1) ^ A)) :=
      mul_le_mul_of_nonneg_left (hc M hM e q K he hq) hS.le
    _ ≤ (M / ((e : ℝ) * Real.sqrt q)) *
        (C / ((M / ((e : ℝ) * q)) ^ 2 * J ^ A)) :=
      mul_le_mul_of_nonneg_left (tail_denominator hY hJ hC K A hcut) hS.le
    _ = C * ((e : ℝ) * q * ((q : ℝ) / Real.sqrt q) / M) / J ^ A := by
      field_simp
    _ = _ := by
      have hroot : (q : ℝ) / Real.sqrt q = Real.sqrt q := by
        apply (div_eq_iff hs.ne').mpr
        nlinarith only [Real.sq_sqrt hqR.le]
      rw [hroot]

end Ostmann

end OAI
