import OAI.NumberTheory.TwoPoint.Fourier.ModFiveSmoothedPsi
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-! Exact finite differences for the triangularly smoothed Mangoldt sum.
The error is confined to the short interval at the upper endpoint. -/

namespace TwoPointCorrelations

open Complex Finset ArithmeticFunction
open scoped BigOperators

lemma modFive_smoothed_scale (χ : DirichletCharacter ℂ 5) {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) * modFiveSmoothedPsi χ x =
      ∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n * ((x - (n : ℝ) : ℝ) : ℂ) := by
  rw [modFiveSmoothedPsi, mul_sum]
  apply sum_congr rfl
  intro n hn
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  push_cast
  field_simp

lemma modFive_smoothed_difference (χ : DirichletCharacter ℂ 5) {x : ℝ}
    (hx : 0 < x) (m : ℕ) :
    (((x + m : ℝ) : ℂ) * modFiveSmoothedPsi χ (x + m) -
      (x : ℂ) * modFiveSmoothedPsi χ x) =
      (m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n) +
        ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
          modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ) := by
  rw [modFive_smoothed_scale χ (by positivity), modFive_smoothed_scale χ hx.ne',
    Nat.floor_add_natCast hx.le]
  have hsplit (f : ℕ → ℂ) :
      (∑ n ∈ Icc 1 (⌊x⌋₊ + m), f n) =
      (∑ n ∈ Icc 1 ⌊x⌋₊, f n) + (∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), f n) := by
    simpa only [Ico_add_one_right_eq_Icc] using
      (sum_Ico_consecutive f (by omega : 1 ≤ ⌊x⌋₊ + 1)
        (by omega : ⌊x⌋₊ + 1 ≤ (⌊x⌋₊ + m) + 1)).symm
  rw [hsplit]
  have hmain :
      (∑ n ∈ Icc 1 ⌊x⌋₊,
        modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ)) -
      (∑ n ∈ Icc 1 ⌊x⌋₊,
        modFiveMangoldtTwist χ n * ((x - (n : ℝ) : ℝ) : ℂ)) =
      (m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n) := by
    rw [← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro n hn
    push_cast
    ring
  linear_combination hmain

lemma modFive_mangoldt_norm_le_log (χ : DirichletCharacter ℂ 5) (n : ℕ) : ‖modFiveMangoldtTwist χ n‖ ≤ Real.log (n : ℝ) := by
  unfold modFiveMangoldtTwist
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) vonMangoldt_nonneg).trans
    (by simpa using (vonMangoldt_le_log (n := n)))

lemma modFive_smoothed_remainder (χ : DirichletCharacter ℂ 5) {x : ℝ}
    (hx : 0 < x) (m : ℕ) :
    ‖∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
      modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ ≤
        (m : ℝ) ^ 2 * Real.log (x + m) := by
  have hy : 0 < x + (m : ℝ) := by positivity
  have hpoint (n : ℕ) (hn : n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) :
      ‖modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ ≤
        Real.log (x + m) * m := by
    obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hn
    have hn1 : 1 ≤ n := by omega
    have hnx : x < (n : ℝ) := (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hnlo)
    have hny : (n : ℝ) ≤ x + m := by
      have hb := Nat.floor_le hx.le
      have hc : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) + m := by exact_mod_cast hnhi
      linarith
    have hwt : 0 ≤ x + m - (n : ℝ) := by linarith
    have hwtm : x + m - (n : ℝ) ≤ (m : ℝ) := by linarith
    have hlog : ‖modFiveMangoldtTwist χ n‖ ≤ Real.log (x + m) :=
      (modFive_mangoldt_norm_le_log χ n).trans
        (Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hny)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwt]
    exact mul_le_mul hlog hwtm hwt (le_trans (norm_nonneg _) hlog)
  have hc : #(Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m)) = m := by
    rw [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
        ‖modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), Real.log (x + m) * m :=
      sum_le_sum hpoint
    _ = _ := by rw [sum_const, hc, nsmul_eq_mul]; ring

lemma modFive_twistedPsi_sum (χ : DirichletCharacter ℂ 5) (x : ℝ) :
    modFiveTwistedPsi χ x = ∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n := by
  have he : (∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n) =
      ∑ n ∈ Icc 0 ⌊x⌋₊, modFiveMangoldtTwist χ n := by
    apply sum_subset
    · intro n hn
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
      exact mem_Icc.mpr ⟨by omega, hnN⟩
    · intro n hn hnot
      have hn0 : n = 0 := by
        have := mem_Icc.mp hn
        have hn1 : ¬1 ≤ n := by
          intro hn1
          exact hnot (mem_Icc.mpr ⟨hn1, this.2⟩)
        omega
      subst n
      simp [modFiveMangoldtTwist]
  rw [he, modFiveTwistedPsi]
  apply sum_congr rfl
  intro n hn
  simp only [modFiveMangoldtTwist, mul_comm]

/-- A completely finite unsmoothing inequality, with the short-interval
cost bounded only by the elementary Mangoldt estimate Λ(n)≤log n. -/
theorem modFive_unsmoothing_bound (χ : DirichletCharacter ℂ 5) {x : ℝ}
    (hx : 0 < x) {m : ℕ} (hm : 0 < m) :
    ‖modFiveTwistedPsi χ x‖ ≤
      ((x + m) * ‖modFiveSmoothedPsi χ (x + m)‖ +
        x * ‖modFiveSmoothedPsi χ x‖ + (m : ℝ) ^ 2 * Real.log (x + m)) / m := by
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have he := modFive_smoothed_difference χ hx m
  have halg : (m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n) =
      (((x + m : ℝ) : ℂ) * modFiveSmoothedPsi χ (x + m) -
        (x : ℂ) * modFiveSmoothedPsi χ x) -
      ∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
        modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ) := by
    linear_combination -he
  rw [modFive_twistedPsi_sum]
  apply (le_div_iff₀ hmp).mpr
  calc
    _ = ‖(m : ℂ) * (∑ n ∈ Icc 1 ⌊x⌋₊, modFiveMangoldtTwist χ n)‖ := by
      rw [norm_mul, Complex.norm_natCast]
      ring
    _ ≤ ‖((x + m : ℝ) : ℂ) * modFiveSmoothedPsi χ (x + m) -
        (x : ℂ) * modFiveSmoothedPsi χ x‖ +
      ‖∑ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m),
        modFiveMangoldtTwist χ n * ((x + m - (n : ℝ) : ℝ) : ℂ)‖ := by
      rw [halg]
      exact norm_sub_le _ _
    _ ≤ (‖((x + m : ℝ) : ℂ) * modFiveSmoothedPsi χ (x + m)‖ +
        ‖(x : ℂ) * modFiveSmoothedPsi χ x‖) + (m : ℝ) ^ 2 * Real.log (x + m) :=
      add_le_add (norm_sub_le _ _) (modFive_smoothed_remainder χ hx m)
    _ = _ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx,
        abs_of_pos (by positivity : 0 < x + (m : ℝ))]

end TwoPointCorrelations

end OAI
