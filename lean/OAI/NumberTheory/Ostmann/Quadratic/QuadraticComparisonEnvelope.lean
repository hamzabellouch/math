import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace OAI

/-! # The numerical minimum in the first recursive quadratic comparison

Here P is the product of the two selected divisor scales and Y is B to the
current sieve exponent. This is the three-term calculation in Heath-Brown,
section 8, equations (19)--(20).
-/

namespace Ostmann

theorem quadratic_comparison_prefactor {M N B P : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hP : 0 < P) :
    let S := M / N * Real.sqrt P * min 1 (N / (Real.sqrt M * Real.sqrt B * P))
    0 ≤ S ∧ S ≤ M / N * Real.sqrt P ∧ S ≤ Real.sqrt M / (Real.sqrt B * Real.sqrt P) := by
  dsimp only
  have hbase : 0 ≤ M / N * Real.sqrt P := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (min_le_left 1 (N / (Real.sqrt M * Real.sqrt B * P))) hbase
  · apply (mul_le_mul_of_nonneg_left
      (min_le_right 1 (N / (Real.sqrt M * Real.sqrt B * P))) hbase).trans
    apply le_of_eq
    have hm := Real.sq_sqrt hM.le
    have hp := Real.sq_sqrt hP.le
    have hsm : Real.sqrt M ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hM)
    have hsb : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
    have hsp : Real.sqrt P ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hP)
    field_simp
    nlinarith

theorem quadratic_comparison_envelope {M N B P Y : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hP : 1 ≤ P) (hY : 0 ≤ Y) :
    (M / N * Real.sqrt P * min 1 (N / (Real.sqrt M * Real.sqrt B * P))) *
      (Y + Real.sqrt (Y * N) + N / Real.sqrt P) ≤
        2 * (M + Real.sqrt M / Real.sqrt B * Y) := by
  have hP₀ : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let S := M / N * Real.sqrt P * min 1 (N / (Real.sqrt M * Real.sqrt B * P))
  let A := Real.sqrt M / Real.sqrt B * Y
  obtain ⟨hS, hS₁, hS₂⟩ := quadratic_comparison_prefactor hM hN hB hP₀
  change 0 ≤ S at hS
  change S ≤ M / N * Real.sqrt P at hS₁
  change S ≤ Real.sqrt M / (Real.sqrt B * Real.sqrt P) at hS₂
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsp : Real.sqrt P ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hP₀)
  have hsb : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  have hsp₁ : 1 ≤ Real.sqrt P := (Real.le_sqrt (by norm_num) hP₀.le).2 (by simpa using hP)
  have hfirst : S * Y ≤ A := by
    apply (mul_le_mul_of_nonneg_right hS₂ hY).trans
    dsimp only [A]
    apply mul_le_mul_of_nonneg_right _ hY
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg M) (Real.sqrt_pos.2 hB)
      (by nlinarith [Real.sqrt_nonneg B])
  have hthird : S * (N / Real.sqrt P) ≤ M := by
    apply (mul_le_mul_of_nonneg_right hS₁ (by positivity)).trans
    apply le_of_eq
    field_simp
  have hSsq : S ^ 2 ≤ (M / N * Real.sqrt P) *
      (Real.sqrt M / (Real.sqrt B * Real.sqrt P)) := by
    simpa only [pow_two] using mul_le_mul hS₁ hS₂ hS (by positivity)
  have hcrosssq : (S * Real.sqrt (Y * N)) ^ 2 ≤ M * A := by
    calc
      _ = S ^ 2 * (Y * N) := by rw [mul_pow, Real.sq_sqrt (mul_nonneg hY hN.le)]
      _ ≤ ((M / N * Real.sqrt P) *
          (Real.sqrt M / (Real.sqrt B * Real.sqrt P))) * (Y * N) :=
        mul_le_mul_of_nonneg_right hSsq (mul_nonneg hY hN.le)
      _ = M * A := by dsimp [A]; field_simp
  have hcross : S * Real.sqrt (Y * N) ≤ (M + A) / 2 := by
    have hc : 0 ≤ S * Real.sqrt (Y * N) := mul_nonneg hS (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg (M - A)]
  change S * (Y + Real.sqrt (Y * N) + N / Real.sqrt P) ≤ 2 * (M + A)
  nlinarith

end Ostmann

end OAI
