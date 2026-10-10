import OAI.Combinatorics.Progressions.Fourier.PrincipalCoefficientResidueSpectrum

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem weighted_integerGridDensity_error_of_tail
    {X O : Type*} [Fintype X] [Fintype O] [DecidableEq O]
    (p : FiniteProbabilityWeights X) (Y : X → O → ℤ) (a : X → ℂ)
    (K M : ℕ) [NeZero M] (cover : Finset (O → Fin M))
    {ε : ℝ} (htail : spectrumTail cover (fun k =>
      ‖p.complexMean (fun x => a x * rectangularGridCharacter M k (Y x))‖) ≤ ε)
    (z : O → ℤ) :
    ‖(K : ℂ) ^ Fintype.card O * p.complexMean
        (fun x => if integerGridResidue M (Y x) = integerGridResidue M z then a x else 0) -
      ((K : ℂ) / M) ^ Fintype.card O * ∑ k ∈ cover,
        p.complexMean (fun x => a x * rectangularGridCharacter M k (Y x)) *
          star (rectangularGridCharacter M k z)‖ ≤
      ((K : ℝ) / M) ^ Fintype.card O * ε := by
  let ψ k := star (rectangularGridCharacter M k z)
  have hψ k : ‖ψ k‖ ≤ 1 := by
    simp only [ψ, norm_star, rectangularGridCharacter_norm, le_refl]
  have hb := (finite_series_truncation_le cover
    (fun k => p.complexMean (fun x => a x * rectangularGridCharacter M k (Y x)))
    ψ hψ).trans htail
  rw [weighted_integerGridDensity_fourier]
  rw [← mul_sub, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end Erdos3

end

end OAI
