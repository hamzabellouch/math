import OAI.NumberTheory.TotientAsymptotic.Renewal

namespace OAI

/-! Cancellation and the strict-slack comparison for the surviving prime indices. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma log_le_a {j : ℕ} (hj : 1 ≤ j) : Real.log (j : ℝ) ≤ a j := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [a_eq_integral]
  have hh := intervalIntegral.integral_mono_on (a := (j : ℝ)) (b := (j+1 : ℝ))
    (by linarith) (intervalIntegrable_const (c := Real.log (j : ℝ)))
    intervalIntegral.intervalIntegrable_log'
    (fun x hx => Real.log_le_log (by linarith) hx.1)
  simpa using hh

lemma a_monotone_positive {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : a i ≤ a j := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · rfl
  · exact (a_le_log hi).trans ((Real.log_le_log (by positivity)
      (by exact_mod_cast hij)).trans (log_le_a (by omega)))

/-- Deleting matching primes cancels exactly their shifts, retaining all
multiplicity in the residual integer. -/
theorem cancel_equal_shifts {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p q : ι → ℕ) (D D' : ℕ)
    (hp : ∀ i ∈ I, 2 ≤ p i)
    (hprod : D*(∏ i ∈ I, (p i-1)) = D'*(∏ i ∈ I, (q i-1))) :
    D*(∏ i ∈ I.filter (fun i => p i ≠ q i), (p i-1)) =
      D'*(∏ i ∈ I.filter (fun i => p i ≠ q i), (q i-1)) := by
  classical
  let C := ∏ i ∈ I.filter (fun i => p i = q i), (p i-1)
  have hC : 0 < C := by
    apply Finset.prod_pos
    intro i hi
    have := hp i (Finset.mem_filter.mp hi).1
    omega
  have hcq : (∏ i ∈ I.filter (fun i => p i = q i), (q i-1)) = C := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hleft : (∏ i ∈ I, (p i-1)) =
      C*(∏ i ∈ I.filter (fun i => p i ≠ q i), (p i-1)) := by
    exact (Finset.prod_filter_mul_prod_filter_not I (fun i => p i=q i) _).symm
  have hright : (∏ i ∈ I, (q i-1)) =
      C*(∏ i ∈ I.filter (fun i => p i ≠ q i), (q i-1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not I (fun i => p i=q i) _, hcq]
  rw [hleft, hright] at hprod
  apply Nat.eq_of_mul_eq_mul_left hC
  nlinarith [hprod]

/-- Removing matched indices and renumbering the survivors cannot increase
the renewal-weighted sum. This is the monotonicity step in collision-slack. -/
theorem reindexed_slack_sum_le (b J : ℕ) (j : ℕ → ℕ) (u : ℕ → ℝ)
    (hj : Set.InjOn j (↑(Finset.Icc 1 b) : Set ℕ))
    (hidx : ∀ k ∈ Finset.Icc 1 b, k ≤ j k ∧ j k ≤ J)
    (hu : ∀ k ∈ Finset.Icc 1 J, 0 ≤ u k) :
    (∑ k ∈ Finset.Icc 1 b, a k*u (j k)) ≤ ∑ k ∈ Finset.Icc 1 J, a k*u k := by
  classical
  have hmem (k : ℕ) (hk : k ∈ Finset.Icc 1 b) : j k ∈ Finset.Icc 1 J :=
    Finset.mem_Icc.mpr ⟨le_trans (Finset.mem_Icc.mp hk).1 (hidx k hk).1, (hidx k hk).2⟩
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 b, a (j k)*u (j k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right
        (a_monotone_positive (Finset.mem_Icc.mp hk).1 (hidx k hk).1)
        (hu _ (hmem k hk))
    _ = ∑ k ∈ (Finset.Icc 1 b).image j, a k*u k := by
      rw [Finset.sum_image]
      exact hj
    _ ≤ ∑ k ∈ Finset.Icc 1 J, a k*u k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
        exact hmem i hi
      · intro k hk _
        exact mul_nonneg (a_pos (Finset.mem_Icc.mp hk).1).le (hu k hk)

end TotientAsymptotic

end

end OAI
