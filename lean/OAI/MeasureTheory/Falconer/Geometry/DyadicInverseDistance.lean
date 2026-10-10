import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

namespace PlanarFalconer

theorem inverse_distance_dyadic {d : ℝ} (hd : 0 < d) (g k : ℕ)
    (hmin : 1/(2:ℝ)^(g+k) ≤ d) :
    1/d ≤ (2:ℝ)^g + ∑ j ∈ Finset.range k,
      if d < 1/(2:ℝ)^(g+j) then (2:ℝ)^(g+j+1) else 0 := by
  induction k with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,add_zero] at *
    apply (div_le_iff₀ hd).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^g)).mp hmin
    nlinarith
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hcoarse : 1/(2:ℝ)^(g+k) ≤ d
    · have hh := ih hcoarse
      have hnon : 0 ≤ (if d < 1/(2:ℝ)^(g+k) then (2:ℝ)^(g+k+1) else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [ite_eq_left (lt_of_not_ge hcoarse)]
      have hfine : 1/d ≤ (2:ℝ)^(g+k+1) := by
        apply (div_le_iff₀ hd).mpr
        have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(g+(k+1)))).mp hmin
        simpa only [Nat.add_assoc,mul_comm] using hh
      have hsum : 0 ≤ ∑ j ∈ Finset.range k,
          if d < 1/(2:ℝ)^(g+j) then (2:ℝ)^(g+j+1) else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> positivity
      have hg : 0 < (2:ℝ)^g := by positivity
      linarith

theorem sum_inverse_distance_dyadic {ι : Type*} (S : Finset ι) (d : ι → ℝ)
    (g k : ℕ) (hd : ∀ i ∈ S, 0 < d i) (hmin : ∀ i ∈ S, 1/(2:ℝ)^(g+k) ≤ d i) :
    ∑ i ∈ S, 1/d i ≤ (S.card:ℝ)*(2:ℝ)^g +
      ∑ j ∈ Finset.range k, ((S.filter fun i => d i < 1/(2:ℝ)^(g+j)).card:ℝ)*(2:ℝ)^(g+j+1) := by
  classical
  calc
    _ ≤ ∑ i ∈ S, ((2:ℝ)^g + ∑ j ∈ Finset.range k,
        if d i < 1/(2:ℝ)^(g+j) then (2:ℝ)^(g+j+1) else 0) :=
      Finset.sum_le_sum (fun i hi => inverse_distance_dyadic (hd i hi) g k (hmin i hi))
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [Finset.sum_const,nsmul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      simp

end PlanarFalconer

end OAI
