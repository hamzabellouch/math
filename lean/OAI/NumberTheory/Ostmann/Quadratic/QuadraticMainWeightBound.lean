import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMainReindex

namespace OAI

/-! # The cutoff saving in the quadratic main-term difference -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticMainGamma_weight_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D K : ℕ, Squarefree D → Odd D → 0 < K → ∀ w : ℕ,
      ‖(quadraticMainGamma D K w : ℂ) / (Real.sqrt (w : ℝ) : ℂ)‖ ≤
        C * ((K * D ^ 2 : ℕ) : ℝ) ^ ε / Real.sqrt (K : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := quadratic_divisor_bound ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro D K hD hDo hK w
  by_cases hz : quadraticMainGamma D K w = 0
  · simp only [hz, Int.cast_zero, zero_div, norm_zero]
    positivity
  obtain ⟨hKw, hwH, _, _⟩ := quadraticMainGamma_support hD hDo hz
  have hw : 0 < w := lt_trans hK hKw
  have hwnorm : ‖(quadraticMainGamma D K w : ℂ)‖ ≤ 2 * (w.divisors.card : ℝ) := by
    rw [Complex.norm_intCast]
    exact_mod_cast quadraticMainGamma_abs_le D K w hw.ne'
  have hn : ‖(quadraticMainGamma D K w : ℂ)‖ ≤
      (2 * C) * ((K * D ^ 2 : ℕ) : ℝ) ^ ε := by
    calc
      _ ≤ 2 * (w.divisors.card : ℝ) := hwnorm
      _ ≤ 2 * (C * (w : ℝ) ^ ε) := mul_le_mul_of_nonneg_left (hdiv w hw.ne') (by norm_num)
      _ ≤ 2 * (C * ((K * D ^ 2 : ℕ) : ℝ) ^ ε) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hwH) hε.le
      _ = _ := by ring
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (2 * C) * ((K * D ^ 2 : ℕ) : ℝ) ^ ε / Real.sqrt (w : ℝ) :=
      div_le_div_of_nonneg_right hn (Real.sqrt_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
      (Real.sqrt_pos.mpr (by exact_mod_cast hK))
      (Real.sqrt_le_sqrt (by exact_mod_cast hKw.le))

 theorem quadraticMainGamma_weighted_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D K : ℕ, Squarefree D → Odd D → 0 < K → ∀ F : ℕ → ℂ,
      ‖∑ w ∈ Finset.Icc 1 (K * D ^ 2),
        (quadraticMainGamma D K w : ℂ) * (F w / (Real.sqrt (w : ℝ) : ℂ))‖ ≤
      (C * ((K * D ^ 2 : ℕ) : ℝ) ^ ε / Real.sqrt (K : ℝ)) *
        ∑ s ∈ D.divisors, ∑ r ∈ oddSquarefreeRange (K * D ^ 2), ‖F (s ^ 2 * r)‖ := by
  obtain ⟨C, hC, hb⟩ := quadraticMainGamma_weight_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro D K hD hDo hK F
  rw [quadraticMainGamma_reindex hD hDo]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have h := mul_le_mul_of_nonneg_right (hb D K hD hDo hK (s ^ 2 * r))
    (norm_nonneg (F (s ^ 2 * r)))
  simpa only [norm_mul, norm_div, div_mul_eq_mul_div, mul_div_assoc, mul_comm ‖F (s ^ 2 * r)‖] using h

end Ostmann

end OAI
