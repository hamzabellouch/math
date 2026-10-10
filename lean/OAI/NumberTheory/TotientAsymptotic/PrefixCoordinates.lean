import OAI.NumberTheory.TotientAsymptotic.PrefixGeometry

namespace OAI

/-! Exact coordinates of the triangular prefix simplex in its slack variables. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prefixSlack_shift (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) (k : ℕ) :
    prefixSlack (N-i) (fun j => u (i+j)) k = prefixSlack N u (i+k) := by
  have hs : (∑ j ∈ Finset.range (N+1),
      if i+k < j then a (j-(i+k))*u j else 0) =
      ∑ j ∈ Finset.range (N-i+1), if k < j then a (j-k)*u (i+j) else 0 := by
    rw [show N+1 = i+(N-i+1) by omega, Finset.sum_range_add]
    have hz : (∑ j ∈ Finset.range i,
        if i+k < j then a (j-(i+k))*u j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.add_lt_add_iff_left, Nat.add_sub_add_left]
  simp only [prefixSlack, hs]

lemma prefix_coordinate_slacks (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) :
    u i = ∑ k ∈ Finset.range (N-i+1), g k*prefixSlack N u (i+k) := by
  have hh := weighted_slack_identity (N-i) (fun j => u (i+j))
  simp only [prefixSlack_shift N u hi, Nat.add_zero] at hh
  exact hh.symm

lemma prefix_coordinate_full_sum (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i < N) :
    u (i+1) = ∑ j ∈ Finset.range N,
      if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0 := by
  rw [prefix_coordinate_slacks N u (by omega : i+1 ≤ N)]
  have hsplit := Finset.sum_range_add
    (fun j => if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0) i (N-i)
  rw [Nat.add_sub_of_le hi.le] at hsplit
  rw [hsplit]
  have hz : (∑ j ∈ Finset.range i,
      if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
  rw [hz, zero_add]
  have he : N-(i+1)+1 = N-i := by omega
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
  congr 2
  omega

/-- The inverse of the determinant-one triangular slack map. -/
theorem prefixLinear_coordinate (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    u i = ∑ j : Fin N,
      if i ≤ j then g (j.val-i.val)*prefixLinear N u j else 0 := by
  have hh := prefix_coordinate_full_sum N (extendPrefix N u) i.isLt
  have hv : extendPrefix N u (i.val+1) = u i := by simp [extendPrefix]
  rw [hv] at hh
  rw [← Fin.sum_univ_eq_sum_range] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← prefixLinear_vector, prefixVector_extend]
  rfl

end TotientAsymptotic

end

end OAI
