import Mathlib.Algebra.Ring.GeomSum
import OAI.NumberTheory.Ostmann.Preliminaries.MertensPrimeBands

namespace OAI

/-! # A uniform reciprocal-log prime budget from the recorded Mertens input -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeReciprocalLogSum (Q : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE Q, 1 / ((p : ℝ) * Real.log p)

noncomputable def primeReciprocalLogConstant (C : ℝ) : ℝ :=
  primeReciprocalLogSum ⌊Real.exp 1⌋₊ + 2 * (1 + Real.log 2 + 2 * max C 0)

theorem primeReciprocalLogBand_le {C : ℝ} (hM : MertensEstimate C)
    (T : ℝ) (hT : 1 ≤ T) :
    (∑ p ∈ logPrimeBand T, 1 / ((p : ℝ) * Real.log p)) ≤
      (1 + Real.log 2 + 2 * max C 0) / T := by
  have hT0 : 0 < T := by linarith
  have hpoint (p) (hp : p ∈ logPrimeBand T) :
      1 / ((p : ℝ) * Real.log p) ≤ (Real.log p / p) / T ^ 2 := by
    obtain ⟨hprime, hlo, _⟩ := logPrimeBand_mem hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hl0 : 0 < Real.log (p : ℝ) := hT0.trans hlo
    calc
      _ = (Real.log p / p) / (Real.log p) ^ 2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (div_nonneg hl0.le hp0.le)
        (sq_pos_of_pos hT0) ((sq_le_sq₀ hT0.le hl0.le).mpr hlo.le)
  have hweight := (logPrimeBand_weight_bounds T C hT hM).2
  have hD : 0 ≤ Real.log 2 + 2 * max C 0 := by
    positivity
  calc
    _ ≤ ∑ p ∈ logPrimeBand T, (Real.log p / p) / T ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = (∑ p ∈ logPrimeBand T, Real.log p / p) / T ^ 2 := (Finset.sum_div ..).symm
    _ ≤ (T + Real.log 2 + 2 * max C 0) / T ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith [le_max_left C 0]
    _ ≤ _ := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hT0) hT0).mpr
      have hh := mul_le_mul_of_nonneg_left hT hD
      nlinarith

theorem primeReciprocalLogSum_mono : Monotone primeReciprocalLogSum := by
  intro Q R hQR
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans hQR,
      Nat.prime_of_mem_primesLE hp⟩
  · intro p _ _
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))

theorem primeReciprocalLogSum_power_budget {C : ℝ} (hM : MertensEstimate C) (N : ℕ) :
    primeReciprocalLogSum ⌊Real.exp ((2 : ℝ) ^ N)⌋₊ ≤
      primeReciprocalLogSum ⌊Real.exp 1⌋₊ +
        (1 + Real.log 2 + 2 * max C 0) * ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hT : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    have hnest : Nat.primesLE ⌊Real.exp ((2 : ℝ) ^ N)⌋₊ ⊆
        Nat.primesLE ⌊Real.exp (2 * (2 : ℝ) ^ N)⌋₊ := by
      intro p hp
      refine Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans ?_, Nat.prime_of_mem_primesLE hp⟩
      apply Nat.floor_mono
      apply Real.exp_le_exp.mpr
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) N]
    have hb := primeReciprocalLogBand_le hM ((2 : ℝ) ^ N) hT
    rw [logPrimeBand, Finset.sum_sdiff_eq_sub hnest] at hb
    change primeReciprocalLogSum ⌊Real.exp (2 * (2 : ℝ) ^ N)⌋₊ -
      primeReciprocalLogSum ⌊Real.exp ((2 : ℝ) ^ N)⌋₊ ≤ _ at hb
    have he : (1 + Real.log 2 + 2 * max C 0) / (2 : ℝ) ^ N =
        (1 + Real.log 2 + 2 * max C 0) * (1 / 2 : ℝ) ^ N := by
      rw [one_div_pow, div_eq_mul_inv, one_div]
    rw [he] at hb
    rw [Finset.sum_range_succ, pow_succ]
    rw [mul_comm ((2 : ℝ) ^ N) 2]
    nlinarith

theorem primeReciprocalLogSum_uniform {C : ℝ} (hM : MertensEstimate C) (Q : ℕ) :
    primeReciprocalLogSum Q ≤ primeReciprocalLogConstant C := by
  have hQ : Q ≤ ⌊Real.exp ((2 : ℝ) ^ Q)⌋₊ := by
    apply Nat.le_floor
    have hn : Q ≤ 2 ^ Q := (Nat.lt_two_pow_self (n := Q)).le
    have hr : (Q : ℝ) ≤ (2 : ℝ) ^ Q := by exact_mod_cast hn
    linarith [Real.add_one_le_exp ((2 : ℝ) ^ Q)]
  have hgeom : (∑ j ∈ Finset.range Q, (1 / 2 : ℝ) ^ j) ≤ 2 := by
    have hh := geom_sum_mul_neg (1 / 2 : ℝ) Q
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) Q]
  have hA : 0 ≤ 1 + Real.log 2 + 2 * max C 0 := by positivity
  exact (primeReciprocalLogSum_mono hQ).trans
    ((primeReciprocalLogSum_power_budget hM Q).trans (by
      unfold primeReciprocalLogConstant
      nlinarith))

end Ostmann

end OAI
