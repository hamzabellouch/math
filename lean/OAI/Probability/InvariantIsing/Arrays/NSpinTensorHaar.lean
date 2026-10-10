import OAI.Probability.InvariantIsing.Arrays.NSpinTensorComparison
import OAI.Probability.InvariantIsing.Haar.HaarVariance

namespace OAI

/-! The Haar variance contribution for the actual tensor-enriched pressure. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

/-- Haar contributes the square of the normalized covariance rotation
modulus divided by volume. The Gaussian and cascade randomness have been
averaged in this observable, using the proved flat mean identity. -/
theorem haar_tensorEnrichedPressure_variance (hpub : HaarConcentrationInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N),
      IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m k : ℕ, ∀ eig c : Fin N → ℝ,
    ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin k → Fin m → ℕ,
    ∀ amplitude : Fin k → ℝ, ∀ n : ℕ, ∀ b : ℕ → ℝ,
      CascadeExponents n b →
    ∀ site : ℕ → ℝ≥0, ∀ monomial : ℕ → Fin k → ℝ≥0,
      let v := fun i => tensorVarianceProfile I degree (site i) (monomial i)
      let F := fun U : SpecialOrthogonal N =>
        tensorEnrichedPressure eig (specialRotation U) c I degree amplitude n b
          (fun i => v (i + 1)) (v 0)
      let L := K + 2 * (N : ℝ)⁻¹ *
        (∑ i : Fin (n + 1), ∑ j, (monomial i j : ℝ) * amplitude j ^ 2 * ∑ a, (degree j a : ℝ))
      MemLp F 2 μ ∧ variance F μ ≤ C * L ^ 2 / N := by
  obtain ⟨C, hC, hvar⟩ := haar_frobeniusLipschitz_variance hpub
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m k eig c K hK heig I degree amplitude n b hb site monomial v F L
  let : IsProbabilityMeasure μ := hμ
  have hNm : 0 < N := by omega
  have hm : Measurable F := measurable_tensorEnrichedPressure eig c I degree amplitude n b _ _
  have hL : 0 < L := by
    dsimp only [L]
    exact add_pos_of_pos_of_nonneg hK (by positivity)
  have hLip : ∀ U V, |F U - F V| ≤ L * frobeniusDistance U V := fun U V =>
    abs_tensorEnrichedPressure_sub_rotation_le hNm eig c U V K hK.le heig
      I degree amplitude n b hb site monomial
  exact ⟨haar_frobeniusLipschitz_memLp_two hpub N hN μ hμinv F hm L hL hLip,
    hvar N hN μ hμ hμinv F hm L hL hLip⟩

end InvariantIsing

end

end OAI
