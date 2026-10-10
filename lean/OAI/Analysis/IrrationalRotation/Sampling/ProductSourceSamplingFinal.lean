import OAI.Analysis.IrrationalRotation.Sampling.ProductSourceSamplingEnergy
import OAI.Analysis.IrrationalRotation.Sampling.ProductSourceSamplingAssembly
import OAI.Analysis.IrrationalRotation.Sampling.ProductSourceSamplingL2
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingSourceWeak
import OAI.Analysis.IrrationalRotation.Product.ProductSourceAngleLaw
import OAI.Analysis.IrrationalRotation.Sampling.ProductScaleSampling

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel.SamplingWeights

theorem ae_hasAllFiniteCoordinateSampling
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      HasAllFiniteCoordinateSampling θ := by
  obtain ⟨N, hN⟩ := hp.exists_sampling_sequence
  filter_upwards [hp.ae_source_angles S hS hblock,
    ae_all_sourceCylinder_energy_tendsto_zero hp N hN S hS hblock,
    ae_all_source_univ_energy_tendsto_zero hp N hN S hS hblock] with θ hθ hC hU
  intro I
  apply orderedOrbitSampling_of_source_limits hp N hN θ I
    (fun i => (hθ.2.1 i).1.le) hθ.2.2.1
    (fun j i hi => (hθ.1 j i hi).2)
  · exact source_hasUniformL2Marginals_of_energy_convergence hp N θ I (hU I)
  · exact source_orbitAverage_weaklyConverges_of_cylinder_energy hp N θ I (hC I)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
