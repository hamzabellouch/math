import OAI.Probability.InvariantIsing.Cavity.CavitySpinObservable
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledModelNumerator
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledModelSpinMean

namespace OAI

/-! The finite-model spin mean is the normalized continuous spectral
observable used in the Haar replica comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_labeled_spin_observable {m d k n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : ∀ i, q i ∈ Icc 0 1)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (j : Fin k)
    (ω : CavityLabeledDisorder d n) :
    cavityWeightedReplicaMean (cavityLabeledPriorKernel n R (uniformSpinPrior k) ω)
      (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
      (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavitySpinObservable Φ hΦ j) (ω,ξ)) =
      cavityLabeledSpinDepthMean n K R L C (fun i => Φ (q (cavityFiniteLevel n i))) j ω := by
  have htest (ξ : Fin 2 → CavityLabeledState d k n) :
      cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavitySpinObservable Φ hΦ j) (ω,ξ) =
        Φ (q (cavityFiniteLevel n (labeledCommonDepth n (ξ 0).1.1 (ξ 1).1.1))) *
          (spinValue ((ξ 0).2 j) * spinValue ((ξ 1).2 j)) :=
    cavitySpinObservable_finite rho lam hrho hsum p q hq Φ hΦ j _ _
  simp only [cavityWeightedReplicaMean, cavityWeightNumerator, cavityWeightNormalizer,
    cavityLabeledSpinDepthMean, referenceReplicaMean, referencePartition, Real.exp_sum, htest]

end InvariantIsing

end

end OAI
