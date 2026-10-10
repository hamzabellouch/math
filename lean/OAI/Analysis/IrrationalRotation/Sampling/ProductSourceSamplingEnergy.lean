import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingSourceAlmostSure
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTestCongruence
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingUnitTests

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel.SamplingWeights
open SamplingCylinderWeak

theorem ae_sourceCylinder_energy_tendsto_zero
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ j in atTop, ProductSamplingPowersAt p j (N j))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      S i = (p.m j : ℝ) * p.K j)
    (I : Finset ℕ) (t : CylinderTest (Bool × ℕ)) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      Tendsto (fun j => ∫ x,
        (sourceTestedError p N false I (cylinderCoordinateSet t false)
          (cylinderCoordinateSet t true) j θ x)^2 ∂baseMeasure) atTop (𝓝 0) := by
  obtain ⟨a, b, c, d, hE, hF, _⟩ := exists_cylinderTest_first_error_rationalIco t
  have hall := ae_all_sourceTestedError (ι := Unit) hp N hN S hS hblock
    (fun _ => false) (fun _ => I)
    (fun _ i => (a i : ℝ)) (fun _ i => (b i : ℝ))
    (fun _ i => (c i : ℝ)) (fun _ i => (d i : ℝ))
  filter_upwards [hall] with θ hθ
  obtain ⟨hf, hsum, hnorm⟩ := hθ ()
  have heq (j : ℕ) := integral_sq_sourceTestedError_first_congr p N I hE hF j θ
  simpa only [heq] using hsum.tendsto_atTop_zero

theorem ae_all_sourceCylinder_energy_tendsto_zero
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ j in atTop, ProductSamplingPowersAt p j (N j))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      ∀ (I : Finset ℕ) (t : CylinderTest (Bool × ℕ)),
      Tendsto (fun j => ∫ x,
        (sourceTestedError p N false I (cylinderCoordinateSet t false)
          (cylinderCoordinateSet t true) j θ x)^2 ∂baseMeasure) atTop (𝓝 0) := by
  exact ae_all_iff.mpr fun I => ae_all_iff.mpr fun t =>
    ae_sourceCylinder_energy_tendsto_zero hp N hN S hS hblock I t

theorem ae_all_source_univ_energy_tendsto_zero
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ j in atTop, ProductSamplingPowersAt p j (N j))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      ∀ (I : Finset ℕ) (endpoint : Bool),
      Tendsto (fun j => ∫ x,
        (sourceTestedError p N endpoint I (fun _ => univ)
          (fun _ => univ) j θ x)^2 ∂baseMeasure) atTop (𝓝 0) := by
  have hall := ae_all_sourceTestedError (ι := Finset ℕ × Bool) hp N hN S hS hblock
    Prod.snd Prod.fst (fun _ _ => 0) (fun _ _ => 1)
    (fun _ _ => 0) (fun _ _ => 1)
  filter_upwards [hall] with θ hθ
  intro I endpoint
  obtain ⟨hf, hsum, hnorm⟩ := hθ (I, endpoint)
  simpa only [sourceTestedError_univ_eq_Ico] using hsum.tendsto_atTop_zero

end Invariant233.ProductModel.SamplingWeights

end

end OAI
