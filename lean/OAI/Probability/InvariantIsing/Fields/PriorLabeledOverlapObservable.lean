import OAI.Probability.InvariantIsing.Fields.PriorLabeledDepthMean
import OAI.Probability.InvariantIsing.Cavity.CavityOverlapObservable

namespace OAI
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators BoundedContinuousFunction
namespace InvariantIsing
lemma prior_cavity_labeled_overlap_observable {m d k n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : ∀ i, q i ∈ Icc 0 1)
    (K R : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    (ω : CavityLabeledDisorder d n) :
    cavityWeightedReplicaMean (cavityLabeledPriorKernel n R π ω)
      (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
      (fun ξ => cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavityOverlapObservable Φ hΦ) (ω,ξ)) =
      priorCavityLabeledDepthMean n K R L C π (fun i => Φ (q (cavityFiniteLevel n i))) ω := by
  have htest (ξ : Fin 2 → CavityLabeledState d k n) :
      cavityLabeledReplicaTest (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q)
        (cavityOverlapObservable Φ hΦ) (ω,ξ) =
        Φ (q (cavityFiniteLevel n (labeledCommonDepth n (ξ 0).1.1 (ξ 1).1.1))) :=
    cavityOverlapObservable_finite rho lam hrho hsum p q hq Φ hΦ _ _
  simp only [cavityWeightedReplicaMean, cavityWeightNumerator, cavityWeightNormalizer,
    priorCavityLabeledDepthMean, referenceReplicaMean, referencePartition, Real.exp_sum, htest]

end InvariantIsing

end

end OAI
