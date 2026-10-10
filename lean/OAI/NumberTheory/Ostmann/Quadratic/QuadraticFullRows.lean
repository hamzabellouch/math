import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRowNorm

namespace OAI

/-! # Passing from disjoint dyadic rows to the full quadratic matrix -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_full_rows_of_dyadic {p ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    {M N : ℕ} (hM : 0 < M)
    (h : ∀ R : ℕ, 0 < R → QuadraticRowBound
      ((oddSquarefreeRange (2 * R)).filter (R ≤ ·)) N
      (C * ((R : ℝ) * N) ^ ε * ((R : ℝ) + (N : ℝ) ^ p))) :
    QuadraticRowBound (oddSquarefreeRange M) N
      ((Nat.log 2 M + 1 : ℕ) * C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + (N : ℝ) ^ p)) := by
  intro v
  have hE : 0 ≤ quadraticSieveEnergy N v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold quadraticRowEnergy
  rw [← quadratic_dyadic_divisors_sum M]
  calc
    _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 M + 1),
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + (N : ℝ) ^ p) * quadraticSieveEnergy N v := by
      apply Finset.sum_le_sum
      intro j hj
      have hR : 0 < 2 ^ j := by positivity
      have hRM : 2 ^ j ≤ M := (Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (by have := Finset.mem_range.mp hj; omega)).trans (Nat.pow_log_le_self 2 (by omega))
      have hsub : quadraticDyadicDivisors M j ⊆
          (oddSquarefreeRange (2 * 2 ^ j)).filter (2 ^ j ≤ ·) := by
        intro m hm
        exact Finset.mem_filter.mpr
          ⟨quadraticDyadicDivisors_subset_double M j hm, (quadraticDyadicDivisors_bounds hm).1⟩
      apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
      apply (h (2 ^ j) hR v).trans
      apply mul_le_mul_of_nonneg_right _ hE
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ hC
        exact Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hRM) (Nat.cast_nonneg N)) hε
      · exact add_le_add (by exact_mod_cast hRM) le_rfl
      · positivity
      · positivity
    _ = _ := by simp; ring

theorem quadratic_sieve_of_row_bound {M N : ℕ} {T : ℝ}
    (h : QuadraticRowBound (oddSquarefreeRange M) N T) : QuadraticSieveBound M N (2 * T) := by
  intro v
  have hv := h v
  have hw := h (reciprocityTwist v)
  rw [quadraticSieveEnergy_reciprocityTwist] at hw
  have htw : reciprocityTwist (reciprocityTwist v) = v := by
    funext n
    simp only [reciprocityTwist]
    split_ifs <;> simp
  have hs : (∑ m ∈ oddSquarefreeRange M, ‖quadraticSieveSum N v m‖ ^ 2) ≤
      quadraticRowEnergy (oddSquarefreeRange M) N v +
        quadraticRowEnergy (oddSquarefreeRange M) N (reciprocityTwist v) := by
    unfold quadraticRowEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m hm
    have ho := (Finset.mem_filter.mp hm).2.1
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ho) with h1 | h3
    · rw [quadraticTransposeSum_one_mod_four N v m h1]
      linarith [sq_nonneg ‖quadraticTransposeSum N (reciprocityTwist v) m‖]
    · rw [quadraticTransposeSum_three_mod_four N (reciprocityTwist v) m h3, htw]
      linarith [sq_nonneg ‖quadraticTransposeSum N v m‖]
  nlinarith only [hs, hv, hw]

end Ostmann

end OAI
