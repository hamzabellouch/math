import OAI.NumberTheory.EgyptianFractions.ThreePrimeMangoldt

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Finite Abel summation: a nonnegative decreasing weight does not enlarge
a uniform partial-sum bound by more than its first value. -/
theorem norm_sum_range_weighted_le_of_partial_sums
    (f : ℕ → ℝ) (g : ℕ → ℂ) (hf : ∀ i, 0 ≤ f i) (hmono : Antitone f)
    (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hpartial : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, g i‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, f i • g i‖ ≤ f 0 * B := by
  by_cases hn : n = 0
  · simp only [hn, Finset.sum_range_zero, norm_zero]
    exact mul_nonneg (hf 0) hB
  rw [Finset.sum_range_by_parts]
  refine (norm_sub_le _ _).trans ?_
  have hlast : ‖f (n - 1) • ∑ i ∈ Finset.range n, g i‖ ≤ f (n - 1) * B := by
    rw [norm_smul, Real.norm_of_nonneg (hf _)]
    exact mul_le_mul_of_nonneg_left (hpartial n le_rfl) (hf _)
  have hrest :
      ‖∑ i ∈ Finset.range (n - 1),
        (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j‖ ≤
      (f 0 - f (n - 1)) * B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n - 1),
          ‖(f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hdec := hmono (Nat.le_succ i)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hdec), neg_sub]
        apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hdec)
        exact hpartial (i + 1) (by have := Finset.mem_range.mp hi; omega)
      _ = _ := by rw [← Finset.sum_mul, Finset.sum_range_sub']
  nlinarith

/-- Logarithmic prime weights may be removed on an interval at a cost of only
`1 / log L`, provided all weighted partial sums on that interval are bounded. -/
theorem norm_prime_interval_sum_le_of_log_partial_sums
    (L n : ℕ) (hL : 2 ≤ L) (w : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hpartial : ∀ k ≤ n,
      ‖∑ p ∈ Finset.Ico L (L + k), (primeLogWeight p : ℂ) * w p‖ ≤ B) :
    ‖∑ p ∈ (Finset.Ico L (L + n)).filter Nat.Prime, w p‖ ≤
      B / Real.log (L : ℝ) := by
  classical
  let f : ℕ → ℝ := fun i => 1 / Real.log (L + i : ℕ)
  let g : ℕ → ℂ := fun i => (primeLogWeight (L + i) : ℂ) * w (L + i)
  have hlog (i : ℕ) : 0 < Real.log (L + i : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < L + i by omega)
  have hf : ∀ i, 0 ≤ f i := fun i => by dsimp [f]; positivity
  have hmono : Antitone f := by
    intro i j hij
    apply one_div_le_one_div_of_le (hlog i)
    apply Real.log_le_log
    · exact_mod_cast (show 0 < L + i by omega)
    · exact_mod_cast Nat.add_le_add_left hij L
  have hpart : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, g i‖ ≤ B := by
    intro k hk
    simpa only [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, g] using hpartial k hk
  have he := norm_sum_range_weighted_le_of_partial_sums f g hf hmono n B hB hpart
  have hcancel (i : ℕ) : f i • g i = if (L + i).Prime then w (L + i) else 0 := by
    dsimp [f, g, primeLogWeight]
    split_ifs with hp
    · rw [← mul_assoc, ← Complex.ofReal_mul,
        one_div_mul_cancel (hlog i).ne', Complex.ofReal_one, one_mul]
    · simp
  simp_rw [hcancel] at he
  rw [Finset.sum_filter, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  convert he using 1
  dsimp [f]
  ring

/-- A short initial segment plus Abel summation converts a uniform bound for
prime-logarithmic prefix sums into an unweighted prime sum bound. -/
theorem norm_prime_sum_le_cutoff_add_log_bound
    (L N : ℕ) (hL : 2 ≤ L) (hLN : L ≤ N) (w : ℕ → ℂ)
    (hw : ∀ p < L, ‖w p‖ ≤ 1) (B : ℝ) (hB : 0 ≤ B)
    (hpartial : ∀ k ≤ N,
      ‖∑ p ∈ Finset.range k, (primeLogWeight p : ℂ) * w p‖ ≤ B) :
    ‖∑ p ∈ (Finset.range N).filter Nat.Prime, w p‖ ≤
      (L : ℝ) + 2 * B / Real.log (L : ℝ) := by
  classical
  have htail := norm_prime_interval_sum_le_of_log_partial_sums L (N - L) hL w
    (2 * B) (by positivity) (by
      intro k hk
      rw [Finset.sum_Ico_eq_sub _ (Nat.le_add_right L k)]
      refine (norm_sub_le _ _).trans ?_
      have h1 := hpartial (L + k) (by omega)
      have h2 := hpartial L hLN
      linarith)
  rw [Nat.add_sub_of_le hLN] at htail
  have hhead : ‖∑ p ∈ (Finset.range L).filter Nat.Prime, w p‖ ≤ (L : ℝ) := by
    calc
      _ ≤ ∑ p ∈ (Finset.range L).filter Nat.Prime, ‖w p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ (Finset.range L).filter Nat.Prime, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hw p (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      _ = (((Finset.range L).filter Nat.Prime).card : ℝ) := by simp
      _ ≤ (L : ℝ) := by
        exact_mod_cast (by simpa only [Finset.card_range] using
          Finset.card_filter_le (Finset.range L) Nat.Prime)
  have hsplit :
      (∑ p ∈ (Finset.range N).filter Nat.Prime, w p) =
      (∑ p ∈ (Finset.range L).filter Nat.Prime, w p) +
        ∑ p ∈ (Finset.Ico L N).filter Nat.Prime, w p := by
    simp only [Finset.sum_filter]
    exact (Finset.sum_range_add_sum_Ico (fun p => if p.Prime then w p else 0) hLN).symm
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hhead htail)

end Problem337

end

end OAI
