import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedSpinTest
import OAI.Probability.InvariantIsing.Cavity.CavityWeakRadialCutoff

namespace OAI

/-! Convergence of hard-restricted spin replica numerators follows from
the joint marked laws at the common continuity radii. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_restricted_spin_replica_tendsto {m r q d k : ℕ}
    (Q : ℕ → ProbabilityMeasure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
    (Q₀ : ProbabilityMeasure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
    (hQ : Tendsto Q atTop (𝓝 Q₀))
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ)
    (hnull : (Q₀ : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
      {z | cavityReplicaRadius J z = B} = 0) :
    Tendsto (fun n => ∫ z, cavityRestrictedSpinReplicaValue K L C T B J π F z
        ∂(Q n : Measure _)) atTop
      (𝓝 (∫ z, cavityRestrictedSpinReplicaValue K L C T B J π F z
        ∂(Q₀ : Measure _))) := by
  rw [cavityRestrictedSpinReplicaValue_eq K L C T hB J π F]
  exact cavity_weak_radial_cutoff_integral Q Q₀ hQ (cavityReplicaRadius J)
    (continuous_cavityReplicaRadius J) (cavityCappedSpinReplicaTest K L C T J π F) B hnull

end InvariantIsing

end

end OAI
