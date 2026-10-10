import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDyadicArithmetic

namespace OAI

/-! # Decaying mean squares for the actual distant dyadic blocks -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityFiniteSquare_dyadic_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ N → 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      10 * (Q : ℝ) * T ≤ N → ∀ j : ℕ,
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ∫ t in Icc (-T) T,
        ‖∑ n ∈ Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N),
          densitySquareIntegralTerm χ (densityVerticalPoint (1 / 2) t) n‖ ^ 2) ≤
          C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * (1 + Real.log N) ^ 3 *
            (j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j := by
  obtain ⟨C, hC, hb⟩ := densityFiniteSquare_tail_mean
  refine ⟨4 * C, by positivity, ?_⟩
  intro N Q hN hQ T hT hscale j F hF
  have hM : 1 ≤ 2 ^ j * N := one_le_mul (by exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)) : 1 ≤ (2 : ℕ) ^ j)) hN
  have hS : Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N) ⊆
      Finset.Icc (2 ^ j * N) (2 ^ (j + 1) * N) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp hn).1.le, (Finset.mem_Ioc.mp hn).2⟩
  have h := hb (2 ^ j * N) (2 ^ (j + 1) * N) Q hM hQ T hT
    (Finset.Ioc (2 ^ j * N) (2 ^ (j + 1) * N)) hS F hF
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hNl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog0 : 0 ≤ 1 + Real.log ((2 : ℝ) ^ (j + 1) * N) := by
    apply le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_add_of_nonneg_right _)
    apply Real.log_nonneg
    have hp : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hlog := pow_le_pow_left₀ hlog0 (density_dyadic_log_bound N j hN) 3
  have hend : (2 : ℝ) ^ (j + 1) * N = 2 * (2 : ℝ) ^ j * N := by rw [pow_succ]; ring
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  calc
    _ ≤ C * ((10 * (Q : ℝ) * T) ^ 2 *
        ((2 : ℝ) ^ (j + 1) * N + (Q : ℝ) ^ 2 * T) *
          (((2 : ℝ) ^ (j + 1) * N) * (1 + Real.log ((2 : ℝ) ^ (j + 1) * N)) ^ 3 /
            ((2 : ℝ) ^ j * N) ^ 3)) := by
      convert h using 1
      ring
    _ ≤ C * (4 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) *
        (1 + Real.log ((2 : ℝ) ^ (j + 1) * N)) ^ 3 / (2 : ℝ) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [hend]
      exact density_dyadic_fraction_bound _ _ _ _ _ (by positivity) hscale hNp
        (by positivity) hr (by simpa only [hend] using hlog0)
    _ ≤ C * (4 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) *
        (((j + 2 : ℝ) * (1 + Real.log N)) ^ 3) / (2 : ℝ) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
