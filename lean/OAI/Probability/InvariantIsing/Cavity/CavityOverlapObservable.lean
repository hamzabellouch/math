import OAI.Probability.InvariantIsing.Cavity.CavityLabeledSpinObservable
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledDepthMean

namespace OAI

/-! The continuous ordinary-overlap observable, without a spin insertion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavityOverlapObservable {m k : ℕ} (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    SpectralBlock m 2 × (Fin 2 → Spin k) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun p => Φ (∑ a, (p.1 0 1 a : ℝ)) ,
      hΦ.comp (continuous_finsetSum _ (fun a _ => by fun_prop))⟩


lemma cavityOverlapObservable_finite {m k n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : ∀ i, q i ∈ Icc 0 1)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    (σ : Fin 2 → LabeledLeaf n) (ε : Fin 2 → Spin k) :
    cavityOverlapObservable (m := m) Φ hΦ
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ, ε) =
      Φ (q (cavityFiniteLevel n (labeledCommonDepth n (σ 0) (σ 1)))) := by
  change Φ (∑ a, (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ 0 1 a : ℝ)) = _
  have hs : (∑ a, (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ 0 1 a : ℝ)) =
      q (cavityFiniteLevel n (labeledCommonDepth n (σ 0) (σ 1))) := by
    simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, Fin.zero_ne_one,
      ↓reduceIte, cavityCanonicalLabel]
    exact sum_cavityCanonicalCoordinate rho lam hrho hsum p (hq _)
  rw [hs]

lemma cavity_labeled_overlap_observable {m d k n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : ∀ i, q i ∈ Icc 0 1)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    (ω : CavityLabeledDisorder d n) :
    cavityWeightedReplicaMean (cavityLabeledPriorKernel n R (uniformSpinPrior k) ω)
      (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
      (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavityOverlapObservable Φ hΦ) (ω,ξ)) =
      cavityLabeledDepthMean n K R L C (fun i => Φ (q (cavityFiniteLevel n i))) ω := by
  have htest (ξ : Fin 2 → CavityLabeledState d k n) :
      cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavityOverlapObservable Φ hΦ) (ω,ξ) =
        Φ (q (cavityFiniteLevel n (labeledCommonDepth n (ξ 0).1.1 (ξ 1).1.1))) :=
    cavityOverlapObservable_finite rho lam hrho hsum p q hq Φ hΦ _ _
  simp only [cavityWeightedReplicaMean, cavityWeightNumerator, cavityWeightNormalizer,
    cavityLabeledDepthMean, referenceReplicaMean, referencePartition, Real.exp_sum, htest]

end InvariantIsing

end

end OAI
