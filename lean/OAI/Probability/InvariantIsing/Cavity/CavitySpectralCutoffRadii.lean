import OAI.Probability.InvariantIsing.Cavity.CavityBlockMarkedLaw
import OAI.Probability.InvariantIsing.Cavity.CavityReplicaRadius
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteGroupSelection
import OAI.Probability.InvariantIsing.Cavity.CavitySelectedReplicaTest

namespace OAI

/-! A single deterministic cutoff sequence avoids the Gaussian-mixture
boundaries for every replica count in the spectral limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_spectral_common_cutoff_radii {m q d : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m+1))) (ρ : Fin m → ℝ)
    (e : Fin d → Fin m × Fin q) :
    ∃ b : ℕ → ℝ, Tendsto b atTop atTop ∧ ∀ j, 0 < b j ∧ ∀ r,
      (cavityBlockMarkedLaw (q := q) Q ρ (cavitySpectralGroupBlock m r) : Measure
        (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
        {z | cavityReplicaRadius (cavitySelectedGroupProjection e) z = b j} = 0 :=
  cavity_replica_common_null_radii (fun r => SpectralBlock m r)
    (fun r => cavityBlockMarkedLaw (q := q) Q ρ (cavitySpectralGroupBlock m r))
    (fun _ => cavitySelectedGroupProjection e)

end InvariantIsing

end

end OAI
