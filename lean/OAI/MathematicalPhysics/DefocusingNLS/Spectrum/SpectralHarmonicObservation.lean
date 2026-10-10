import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicEnergy

namespace OAI

/-! The fixed-harmonic pair space, compact observation, and closed core constraint. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable abbrev SpectralHarmonicPair (ell : ℕ) (R : ℝ) :=
  WithLp 2 (SpectralHarmonicEnergy ell R × SpectralHarmonicEnergy ell R)

noncomputable instance spectralHarmonicPair_realInner (ell : ℕ) (R : ℝ) :
    InnerProductSpace ℝ (SpectralHarmonicPair ell R) := InnerProductSpace.complexToReal

noncomputable def spectralHarmonicPairForget (ell : ℕ) (R : ℝ) :
    SpectralHarmonicPair ell R →L[ℂ] SpectralRadialPairEnergy R :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralRadialEnergy R)
    (SpectralRadialEnergy R)).symm.toContinuousLinearMap.comp
      (((spectralHarmonicRadialForget ell R).comp
        (WithLp.fstL 2 ℂ (SpectralHarmonicEnergy ell R) (SpectralHarmonicEnergy ell R))).prod
       ((spectralHarmonicRadialForget ell R).comp
        (WithLp.sndL 2 ℂ (SpectralHarmonicEnergy ell R) (SpectralHarmonicEnergy ell R))))

noncomputable def spectralHarmonicObservation (ell : ℕ) (R : ℝ) (hR : 0 < R) :
    SpectralHarmonicPair ell R →L[ℂ] SpectralRadialObservationSpace R :=
  (spectralRadialObservation R hR).comp (spectralHarmonicPairForget ell R)

theorem spectralHarmonicObservation_compact (ell : ℕ) (R : ℝ) (hR : 0 < R) :
    IsCompactOperator (spectralHarmonicObservation ell R hR) :=
  (spectralRadialObservation_compact R hR).comp_clm _

noncomputable def spectralHarmonicFirstValue (ell : ℕ) (R : ℝ) :
    SpectralHarmonicPair ell R →L[ℝ] SpectralRadialL2 R :=
  (spectralRadialFirstValue R).comp ((spectralHarmonicPairForget ell R).restrictScalars ℝ)

noncomputable def spectralHarmonicCoreSubspace (ell : ℕ) (R l : ℝ) :
    Submodule ℝ (SpectralHarmonicPair ell R) :=
  ((spectralRadialCoreMask R l).comp (spectralHarmonicFirstValue ell R)).ker

noncomputable abbrev SpectralHarmonicCore (ell : ℕ) (R l : ℝ) :=
  spectralHarmonicCoreSubspace ell R l

noncomputable instance spectralHarmonicCore_normedSpace (ell : ℕ) (R l : ℝ) :
    NormedSpace ℝ (SpectralHarmonicCore ell R l) := Submodule.normedSpace _

noncomputable instance spectralHarmonicCore_inner (ell : ℕ) (R l : ℝ) :
    InnerProductSpace ℝ (SpectralHarmonicCore ell R l) := Submodule.innerProductSpace _

instance spectralHarmonicCore_complete (ell : ℕ) (R l : ℝ) :
    CompleteSpace (SpectralHarmonicCore ell R l) := by
  change CompleteSpace (((spectralRadialCoreMask R l).comp
    (spectralHarmonicFirstValue ell R)).ker)
  infer_instance

theorem spectralHarmonicCore_mem (ell : ℕ) (R l : ℝ) (u : SpectralHarmonicPair ell R) :
    u ∈ spectralHarmonicCoreSubspace ell R l ↔
      (fun r => spectralHarmonicFirstValue ell R u r) =ᵐ[
        (radialPressureMeasure R).restrict (Iic l)] 0 :=
  spectralRadialCoreMask_zero R l (spectralHarmonicFirstValue ell R u)

end DefocusingNLS

end OAI
