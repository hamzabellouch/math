import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OAI

/-! # Finite dyadic inverse-power sums at the critical ambient exponent -/

namespace Falconer

theorem inverse_power_dyadic {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (g k : ℕ)
    (hmin : 1/(2:ℝ)^(g+k) ≤ r) :
    (1/r)^s ≤ ((2:ℝ)^g)^s + ∑ j ∈ Finset.range k,
      if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
  induction k with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,add_zero] at *
    apply Real.rpow_le_rpow (by positivity) _ hs
    apply (div_le_iff₀ hr).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^g)).mp hmin
    nlinarith
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hc : 1/(2:ℝ)^(g+k) ≤ r
    · have hh := ih hc
      have hn : 0 ≤ (if r < 1/(2:ℝ)^(g+k) then ((2:ℝ)^(g+k+1))^s else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [ite_eq_left (lt_of_not_ge hc)]
      have hinv : 1/r ≤ (2:ℝ)^(g+k+1) := by
        apply (div_le_iff₀ hr).mpr
        have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(g+(k+1)))).mp hmin
        simpa only [Nat.add_assoc,mul_comm] using hh
      have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1/r) hinv hs
      have hsum : 0 ≤ ∑ j ∈ Finset.range k,
          if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> positivity
      have hz : 0 ≤ ((2:ℝ)^g)^s := by positivity
      linarith

theorem sum_inverse_power_dyadic {ι : Type*} (S : Finset ι) (r : ι → ℝ)
    {s : ℝ} (hs : 0 ≤ s) (g k : ℕ)
    (hr : ∀ i ∈ S, 0 < r i) (hmin : ∀ i ∈ S, 1/(2:ℝ)^(g+k) ≤ r i) :
    (∑ i ∈ S, (1/r i)^s) ≤ (S.card:ℝ)*((2:ℝ)^g)^s +
      ∑ j ∈ Finset.range k,
        ((S.filter fun i => r i < 1/(2:ℝ)^(g+j)).card:ℝ)*((2:ℝ)^(g+j+1))^s := by
  classical
  calc
    _ ≤ ∑ i ∈ S, (((2:ℝ)^g)^s+∑ j ∈ Finset.range k,
        if r i < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0) :=
      Finset.sum_le_sum (fun i hi => inverse_power_dyadic (hr i hi) hs g k (hmin i hi))
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [Finset.sum_const,nsmul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      simp

end Falconer

end OAI
