import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

namespace Zarankiewicz
open scoped BigOperators

theorem triangular_degree_sum (ell : ℕ → ℕ) (m : ℕ) :
    (∑ h ∈ Finset.range m, ∑ e ∈ Finset.range (h+1), e * ell e) =
      ∑ e ∈ Finset.range m, e * (m-e) * ell e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel_left, mul_one]
    have hc : ∀ e ∈ Finset.range m,
        e * (m+1-e) * ell e = e * (m-e) * ell e + e * ell e := by
      intro e he
      have ht : m+1-e = (m-e)+1 := by have := Finset.mem_range.mp he; omega
      rw [ht]
      ring
    simp_rw [Finset.sum_congr rfl hc, Finset.sum_add_distrib]
    omega

theorem parabola_le_floor (m e : ℕ) (he : e ≤ m) : e * (m-e) ≤ m*m/4 := by
  have hm : ((m-e : ℕ) : ℤ) + (e : ℤ) = (m : ℤ) := by
    exact_mod_cast Nat.sub_add_cancel he
  have hz : (4 : ℤ) * (e : ℤ) * ((m-e : ℕ) : ℤ) ≤ (m : ℤ) * (m : ℤ) := by
    nlinarith [sq_nonneg ((e : ℤ) - ((m-e : ℕ) : ℤ))]
  have hn : 4 * e * (m-e) ≤ m*m := by exact_mod_cast hz
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  nlinarith

theorem total_degree_cost_le (ell : ℕ → ℕ) (m N : ℕ)
    (hell : ∑ e ∈ Finset.range m, ell e ≤ N) :
    (∑ h ∈ Finset.range m, ∑ e ∈ Finset.range (h+1), e * ell e) ≤ (m*m/4) * N := by
  rw [triangular_degree_sum]
  calc
    (∑ e ∈ Finset.range m, e * (m-e) * ell e) ≤
        ∑ e ∈ Finset.range m, (m*m/4) * ell e := by
      apply Finset.sum_le_sum
      intro e he
      exact Nat.mul_le_mul_right (ell e) (parabola_le_floor m e (Nat.le_of_lt (Finset.mem_range.mp he)))
    _ = (m*m/4) * ∑ e ∈ Finset.range m, ell e := (Finset.mul_sum ..).symm
    _ ≤ (m*m/4) * N := Nat.mul_le_mul_left _ hell

end Zarankiewicz

end OAI
