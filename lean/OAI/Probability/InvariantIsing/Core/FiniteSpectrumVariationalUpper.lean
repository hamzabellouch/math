import OAI.Probability.InvariantIsing.Core.FiniteSpectrumUpper
import OAI.Probability.InvariantIsing.Core.FiniteVariationalBounds

namespace OAI

/-! The finite-spectrum pressure upper bound after taking the path infimum. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_meanPressure_variational_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        rotatedPressure (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
      (variationalFunctional (finiteR ρ lam hρpos hρsum)).toReal + ε := by
  intro ε hε
  obtain ⟨p, S, hS, hp⟩ := exists_finiteEntropy_trial_near_finiteVariational
    ρ lam hρpos hρsum (half_pos hε)
  have hup := finiteSpectrum_meanPressure_upper hhaar hgauss N hN hNlim m μ hμinv
    eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ p S hS.le (ε / 2) (half_pos hε)
  filter_upwards [hup] with k hk
  linarith

end InvariantIsing

end

end OAI
