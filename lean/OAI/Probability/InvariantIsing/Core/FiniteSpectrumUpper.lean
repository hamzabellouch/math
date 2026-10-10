import OAI.Probability.InvariantIsing.Core.FiniteSpectrumStepUpper
import OAI.Probability.InvariantIsing.Core.TrialGridApproximation

namespace OAI

/-! Manuscript Proposition up:bound, in the equivalent eventual-epsilon
form against every trial of finite entropy. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_meanPressure_upper
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
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    (p : OverlapPath) (S : ℝ) (hS : entropyFunctional p ≤ (S : EReal)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        rotatedPressure (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
      S + spectralFunctional (finiteR ρ lam hρpos hρsum) p + ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hgrid := lowerGridPath_spectral_tendsto ρ lam hρpos hρsum p
  obtain ⟨n, hn⟩ := (hgrid.eventually (gt_mem_nhds
    (show spectralFunctional (finiteR ρ lam hρpos hρsum) p <
      spectralFunctional (finiteR ρ lam hρpos hρsum) p + ε / 2 by linarith))).exists
  have hup := finiteSpectrum_meanPressure_step_upper hhaar hgauss N hN hNlim m n
    μ hμinv eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
    (uniformCut n) (uniformCut_strict n) (uniformCut_zero n) (uniformCut_last n)
    (lowerGridPath p n)
    (fun i => (1 - 1 / (n + 1 : ℕ)) * p ((i.val : ℝ) / (n + 1 : ℕ)))
    (lowerGridPath_on_cell p n) (1 / (n + 1 : ℕ)) (by positivity)
    (ae_of_all _ (lowerGridPath_below_one p n)) S
    ((lowerGridPath_entropy_le p n).trans hS) (ε / 2) hhalf
  filter_upwards [hup] with k hk
  linarith

end InvariantIsing

end

end OAI
