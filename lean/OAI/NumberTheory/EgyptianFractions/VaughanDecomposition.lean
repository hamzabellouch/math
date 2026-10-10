import OAI.NumberTheory.EgyptianFractions.VaughanTypeI

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Problem337.Vaughan

/-- Taking a short part restricts a finite weighted sum to the smaller interval. -/
theorem weightedSum_shortPart (N V : ℕ) (w : ℕ → ℂ) (f : ArithmeticFunction ℝ) :
    weightedSum (Finset.Ioc 0 N) w (shortPart V f) =
      weightedSum (Finset.Ioc 0 (min V N)) w f := by
  unfold weightedSum
  calc
    _ = ∑ n ∈ Finset.Ioc 0 (min V N), (shortPart V f n : ℂ) * w n := by
      symm
      apply Finset.sum_subset
      · intro n hn
        obtain ⟨hn0, hnVN⟩ := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨hn0, (le_min_iff.mp hnVN).2⟩
      · intro n hn hnot
        have hV : ¬ n ≤ V := by
          simp only [Finset.mem_Ioc] at hn hnot
          omega
        simp [hV]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [(le_min_iff.mp (Finset.mem_Ioc.mp hn).2).1]

/-- The initial von Mangoldt segment has the elementary `V log V` bound. -/
theorem norm_short_vonMangoldt_sum_le (N V : ℕ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ Finset.Ioc 0 N, ‖w n‖ ≤ 1) :
    ‖weightedSum (Finset.Ioc 0 N) w (shortPart V Λ)‖ ≤
      (V : ℝ) * Real.log V := by
  rw [weightedSum_shortPart]
  unfold weightedSum
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 (min V N), ‖(Λ n : ℂ) * w n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc 0 (min V N), Real.log V := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn0, hnVN⟩ := Finset.mem_Ioc.mp hn
      obtain ⟨hnV, hnN⟩ := le_min_iff.mp hnVN
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      calc
        Λ n * ‖w n‖ ≤ Λ n * 1 := mul_le_mul_of_nonneg_left
          (hw n (Finset.mem_Ioc.mpr ⟨hn0, hnN⟩)) ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ Real.log n := by simpa using (ArithmeticFunction.vonMangoldt_le_log (n := n))
        _ ≤ Real.log V := Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnV)
    _ = (min V N : ℕ) * Real.log V := by simp
    _ ≤ (V : ℝ) * Real.log V := mul_le_mul_of_nonneg_right
      (by exact_mod_cast min_le_left V N) (Real.log_natCast_nonneg V)

/-- The actual Type II term is a hyperbola with both short factors removed. -/
theorem typeII_eq_hyperbola (N U V : ℕ) (w : ℕ → ℂ) :
    weightedSum (Finset.Ioc 0 N) w (typeIICoefficient U * longPart V Λ) =
      ∑ d ∈ (hyperbola N).filter (fun d => U < d.1 ∧ V < d.2),
        (typeIICoefficient U d.1 : ℂ) * (Λ d.2 : ℂ) * w (d.1 * d.2) := by
  unfold weightedSum
  rw [← positive_interval N, sum_real_convolution_hyperbola, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hU : U < d.1
  · by_cases hV : V < d.2 <;> simp [hU, hV]
  · simp [hU, typeIICoefficient_eq_zero U d.1 (not_lt.mp hU)]

/-- A fully finite Vaughan estimate. Only the displayed elementary inner-sum
envelopes are hypotheses; the remaining Type II sum is retained explicitly. -/
theorem norm_vonMangoldt_sum_le (N U V : ℕ) (w : ℕ → ℂ) (B₁ B₂ : ℕ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc 0 N, ‖w n‖ ≤ 1)
    (hfirst : ∀ a ∈ Finset.Ioc 0 (min U N), ∀ k ≤ N / a,
      ‖∑ b ∈ Finset.Ioc 0 k, w (a * b)‖ ≤ B₁ a)
    (hsecond : ∀ a ∈ Finset.Ioc 0 (min (U * V) N),
      ‖∑ b ∈ Finset.Ioc 0 (N / a), w (a * b)‖ ≤ B₂ a) :
    ‖weightedSum (Finset.Ioc 0 N) w Λ‖ ≤
      (V : ℝ) * Real.log V +
      2 * Real.log N * (∑ a ∈ Finset.Ioc 0 (min U N), B₁ a) +
      Real.log N * (∑ a ∈ Finset.Ioc 0 (min (U * V) N), B₂ a) +
      ‖∑ d ∈ (hyperbola N).filter (fun d => U < d.1 ∧ V < d.2),
        (typeIICoefficient U d.1 : ℂ) * (Λ d.2 : ℂ) * w (d.1 * d.2)‖ := by
  have h0 := norm_short_vonMangoldt_sum_le N V w hw
  have h1 := first_typeI_bound w N U B₁ hfirst
  have h2 := second_typeI_bound w N U V B₂ hsecond
  rw [weighted_identity (Finset.Ioc 0 N) w U V]
  calc
    _ ≤ (‖weightedSum (Finset.Ioc 0 N) w (shortPart V Λ)‖ +
          ‖weightedSum (Finset.Ioc 0 N) w
            (shortPart U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)‖) +
        ‖weightedSum (Finset.Ioc 0 N) w (typeICoefficient U V * ζ)‖ +
        ‖weightedSum (Finset.Ioc 0 N) w (typeIICoefficient U * longPart V Λ)‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (norm_sub_le _ _).trans
      exact add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by
      rw [typeII_eq_hyperbola]
      exact add_le_add (add_le_add (add_le_add h0 h1) h2) le_rfl

end Problem337.Vaughan

end

end OAI
