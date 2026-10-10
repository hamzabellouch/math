import OAI.NumberTheory.EgyptianFractions.HyperbolaTypeII
import OAI.NumberTheory.EgyptianFractions.VaughanNearRational

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.VaughanBilinear

/-- A full Type-II estimate for the actual hyperbolic region `m*n ≤ X`.
The rational approximation is the only analytic input: support intersection,
geometric cancellation, harmonic spacing, and coefficient-energy estimates
are all supplied by checked lemmas. Empty row and column intervals are allowed. -/
theorem near_rational_hyperbolic_bilinear_sq_le
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X L U V N : ℕ) (t : Finset ℕ)
    (ht : t ⊆ Finset.Ico V (V + N)) (hpos : ∀ n ∈ t, 0 < n)
    (c b : ℕ → ℂ) :
    ‖∑ m ∈ Finset.Icc L U, c m * ∑ n ∈ t,
      b n * HyperbolaCorrelation.column θ X n m‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc L U, ‖c m‖ ^ 2) *
        ((2 * (N : ℝ) / q + 1) *
          (2 * ((U + 1 - L : ℕ) : ℝ) +
            4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))) *
              (∑ n ∈ t, ‖b n‖ ^ 2) := by
  apply norm_bilinear_sq_le_energy
  intro n hn
  calc
    _ ≤ ∑ k ∈ t, geometricBound (U + 1 - L) (θ * ((n : ℝ) - k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact HyperbolaCorrelation.column_correlation_le θ X L U n k
        ((hpos n hn).trans_le (le_max_left _ _))
    _ ≤ _ := by
      simpa only [Int.cast_sub, Int.cast_natCast] using
        (sum_geometricBound_difference_le θ a q hq hcop happrox
          (U + 1 - L) t (fun k : ℕ => (k : ℤ)) (V : ℤ) N
          (by
            intro k hk
            obtain ⟨hl, hu⟩ := Finset.mem_Ico.mp (ht hk)
            apply Finset.mem_Ico.mpr
            constructor <;> exact_mod_cast (by assumption))
          (by
            intro i hi j hj hij
            dsimp at hij
            exact_mod_cast hij)
          (n : ℤ))

end Problem337.VaughanBilinear

end

end OAI
