import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicForm
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoerciveRestriction

namespace OAI

/-! The limiting weighted inverse on the closed core domain. -/

open InnerProductSpace MeasureTheory
namespace DefocusingNLS

noncomputable def spectralHarmonicCoreInverse (ell : ℕ) (R l : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r) :
    StrongDual ℝ (SpectralHarmonicPair ell R) →L[ℝ] SpectralHarmonicPair ell R :=
  spectralRestrictedInverse (spectralHarmonicCoreSubspace ell R l)
    (spectralHarmonicPairForm ell R w) c hc (spectralHarmonicPairForm_lower ell R w c hcr hca)

theorem spectralHarmonicCoreInverse_mem (ell : ℕ) (R l : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) :
    spectralHarmonicCoreInverse ell R l w c hc hcr hca F ∈ spectralHarmonicCoreSubspace ell R l :=
  spectralRestrictedInverse_mem (spectralHarmonicCoreSubspace ell R l)
    (spectralHarmonicPairForm ell R w) c hc (spectralHarmonicPairForm_lower ell R w c hcr hca) F

theorem spectralHarmonicCoreInverse_equation (ell : ℕ) (R l : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) (v : SpectralHarmonicCore ell R l) :
    spectralHarmonicPairForm ell R w (spectralHarmonicCoreInverse ell R l w c hc hcr hca F) v=F v :=
  spectralRestrictedInverse_equation (spectralHarmonicCoreSubspace ell R l)
    (spectralHarmonicPairForm ell R w) c hc (spectralHarmonicPairForm_lower ell R w c hcr hca) F v

theorem spectralHarmonicCoreInverse_unique (ell : ℕ) (R l : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) (u : SpectralHarmonicPair ell R)
    (hu : u ∈ spectralHarmonicCoreSubspace ell R l)
    (he : ∀ v : SpectralHarmonicCore ell R l, spectralHarmonicPairForm ell R w u v=F v) :
    u=spectralHarmonicCoreInverse ell R l w c hc hcr hca F := by
  exact spectralRestrictedInverse_unique (spectralHarmonicCoreSubspace ell R l)
    (spectralHarmonicPairForm ell R w) c hc (spectralHarmonicPairForm_lower ell R w c hcr hca) F u hu he

theorem spectralHarmonicCoreInverse_norm (ell : ℕ) (R l : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) :
    ‖spectralHarmonicCoreInverse ell R l w c hc hcr hca F‖ ≤ ‖F‖/c := by
  exact spectralRestrictedInverse_norm (spectralHarmonicCoreSubspace ell R l)
    (spectralHarmonicPairForm ell R w) c hc (spectralHarmonicPairForm_lower ell R w c hcr hca) F

theorem spectralHarmonicCoreInverse_observation_compact (ell : ℕ) (R l : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r) :
    IsCompactOperator (((spectralHarmonicObservation ell R hR).restrictScalars ℝ).comp
      (spectralHarmonicCoreInverse ell R l w c hc hcr hca)) :=
  (spectralHarmonicObservation_compact ell R hR).comp_clm _

end DefocusingNLS

end OAI
