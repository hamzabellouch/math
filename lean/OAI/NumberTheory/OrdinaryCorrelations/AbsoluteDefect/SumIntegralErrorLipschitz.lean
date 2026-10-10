import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset

namespace OrdinaryLogIntegral

theorem sum_integral_error_lipschitz (F : ℝ → ℂ) (a : ℝ) (N : ℕ) {L : ℝ}
    (hL : 0 ≤ L)
    (hcont : ContinuousOn F (Set.Icc a (a+N)))
    (hLip : ∀ x ∈ Set.Icc a (a+N), ∀ y ∈ Set.Icc a (a+N), ‖F x-F y‖ ≤ L*|x-y|) :
    ‖(∑ n ∈ Finset.range N, F (a+n)) - ∫ x in a..a+N, F x‖ ≤ N * L := by
  have hsub (n : ℕ) (hn : n < N) :
      Set.uIcc (a+n) (a+(n+1 : ℕ)) ⊆ Set.Icc a (a+N) := by
    rw [Set.uIcc_of_le (by push_cast; linarith)]
    intro x hx
    have hn' : (n+1 : ℝ) ≤ N := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    constructor <;> push_cast at hx <;> linarith [hx.1, hx.2]
  have hi (n : ℕ) (hn : n < N) :
      IntervalIntegrable F volume (a+n) (a+(n+1 : ℕ)) :=
    (hcont.mono (hsub n hn)).intervalIntegrable
  have hsum : (∑ n ∈ Finset.range N, ∫ x in a+n..a+(n+1 : ℕ), F x) =
      ∫ x in a..a+N, F x := by
    simpa only [Nat.cast_zero, add_zero] using
      (intervalIntegral.sum_integral_adjacent_intervals (a := fun n => a+(n : ℝ)) hi)
  rw [← hsum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.range N, L := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_range.mp hn
      have he : F (a+n) - ∫ x in a+n..a+(n+1 : ℕ), F x =
          ∫ x in a+n..a+(n+1 : ℕ), F (a+n) - F x := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const (hi n hn'),
          intervalIntegral.integral_const]
        simp only [Nat.cast_add, Nat.cast_one]
        have hh : a + ((n : ℝ)+1) - (a+n) = 1 := by ring
        rw [hh, one_smul]
      rw [he]
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a+(n : ℝ)) (b := a+(n+1 : ℕ)) (C := L) (f := fun x => F (a+n)-F x)
      have hlocal : ∀ x ∈ Set.uIoc (a+n) (a+(n+1 : ℕ)), ‖F (a+n)-F x‖ ≤ L := by
        intro x hx
        have hn0 : a+n ∈ Set.Icc a (a+N) := hsub n hn' (Set.left_mem_uIcc)
        have hx0 := hsub n hn' (Set.uIoc_subset_uIcc hx)
        have hmv := hLip x hx0 (a+n) hn0
        have hlen : ‖x - (a+n)‖ ≤ 1 := by
          rw [Set.uIoc_of_le (by push_cast; linarith)] at hx
          rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
          push_cast at hx
          linarith [hx.2]
        rw [norm_sub_rev]
        rw [Real.norm_eq_abs] at hlen
        exact hmv.trans (by nlinarith)
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_add_left_eq_sub, add_sub_cancel_left,
        abs_one, mul_one] using hh hlocal
    _ = _ := by simp [mul_comm]

end OrdinaryLogIntegral

end

end OAI
