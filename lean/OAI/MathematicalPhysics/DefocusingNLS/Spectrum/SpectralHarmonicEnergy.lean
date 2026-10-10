import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAngularMeasure
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialObservation

namespace OAI

/-! Completed fixed-harmonic energy, including its exact angular-gradient contribution. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

noncomputable abbrev SpectralAngularL2 (R : ℝ) := Lp ℂ 2 (spectralAngularMeasure R)

noncomputable def spectralSmoothAngularValue (R : ℝ) : 𝓢(ℝ,ℂ) →L[ℂ] SpectralAngularL2 R :=
  (BoundedContinuousFunction.toLp 2 (spectralAngularMeasure R) ℂ).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)

noncomputable abbrev SpectralHarmonicJet (R : ℝ) :=
  WithLp 2 (SpectralRadialJetSpace R × SpectralAngularL2 R)

noncomputable def spectralSmoothHarmonicJet (ell : ℕ) (R : ℝ) :
    𝓢(ℝ,ℂ) →L[ℂ] SpectralHarmonicJet R :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralRadialJetSpace R) (SpectralAngularL2 R)).symm.toContinuousLinearMap.comp
    ((spectralRadialSmoothJet R).prod
      (((Real.sqrt ((ell : ℝ)*(ell+10)) : ℝ) : ℂ) • spectralSmoothAngularValue R))

noncomputable def spectralHarmonicSubspace (ell : ℕ) (R : ℝ) : Submodule ℂ (SpectralHarmonicJet R) :=
  (LinearMap.range (spectralSmoothHarmonicJet ell R).toLinearMap).topologicalClosure

noncomputable abbrev SpectralHarmonicEnergy (ell : ℕ) (R : ℝ) := spectralHarmonicSubspace ell R

instance spectralHarmonicEnergy_complete (ell : ℕ) (R : ℝ) :
    CompleteSpace (SpectralHarmonicEnergy ell R) :=
  Submodule.topologicalClosure.completeSpace _

noncomputable instance spectralHarmonicEnergy_realInner (ell : ℕ) (R : ℝ) :
    InnerProductSpace ℝ (SpectralHarmonicEnergy ell R) := InnerProductSpace.complexToReal

noncomputable def spectralHarmonicSmoothEmbedding (ell : ℕ) (R : ℝ) :
    𝓢(ℝ,ℂ) →L[ℂ] SpectralHarmonicEnergy ell R :=
  (spectralSmoothHarmonicJet ell R).codRestrict (spectralHarmonicSubspace ell R) (fun f =>
    (LinearMap.range (spectralSmoothHarmonicJet ell R).toLinearMap).le_topologicalClosure ⟨f,rfl⟩)

private theorem harmonicJet_radial_mem (ell : ℕ) (R : ℝ) (u : SpectralHarmonicEnergy ell R) :
    (u : SpectralHarmonicJet R).fst ∈ spectralRadialEnergySubspace R := by
  let P := WithLp.fstL 2 ℂ (SpectralRadialJetSpace R) (SpectralAngularL2 R)
  have h : LinearMap.range (spectralSmoothHarmonicJet ell R).toLinearMap ≤
      (spectralRadialEnergySubspace R).comap P.toLinearMap := by
    rintro _ ⟨f,rfl⟩
    change spectralRadialSmoothJet R f ∈ spectralRadialEnergySubspace R
    exact (LinearMap.range (spectralRadialSmoothJet R).toLinearMap).le_topologicalClosure ⟨f,rfl⟩
  have hc : IsClosed (((spectralRadialEnergySubspace R).comap P.toLinearMap :
      Submodule ℂ (SpectralHarmonicJet R)) : Set (SpectralHarmonicJet R)) :=
    (LinearMap.range (spectralRadialSmoothJet R).toLinearMap).isClosed_topologicalClosure.preimage P.continuous
  exact (LinearMap.range (spectralSmoothHarmonicJet ell R).toLinearMap).topologicalClosure_minimal h hc u.property

noncomputable def spectralHarmonicRadialForget (ell : ℕ) (R : ℝ) :
    SpectralHarmonicEnergy ell R →L[ℂ] SpectralRadialEnergy R :=
  ((WithLp.fstL 2 ℂ (SpectralRadialJetSpace R) (SpectralAngularL2 R)).comp
    (spectralHarmonicSubspace ell R).subtypeL).codRestrict
      (spectralRadialEnergySubspace R) (harmonicJet_radial_mem ell R)

noncomputable def spectralHarmonicAngularValue (ell : ℕ) (R : ℝ) :
    SpectralHarmonicEnergy ell R →L[ℂ] SpectralAngularL2 R :=
  (WithLp.sndL 2 ℂ (SpectralRadialJetSpace R) (SpectralAngularL2 R)).comp
    (spectralHarmonicSubspace ell R).subtypeL

theorem spectralHarmonicEnergy_norm_sq (ell : ℕ) (R : ℝ) (u : SpectralHarmonicEnergy ell R) :
    ‖u‖^2=‖spectralHarmonicRadialForget ell R u‖^2+‖spectralHarmonicAngularValue ell R u‖^2 := by
  change ‖(u : SpectralHarmonicJet R)‖^2=
    ‖(u : SpectralHarmonicJet R).fst‖^2+‖(u : SpectralHarmonicJet R).snd‖^2
  exact WithLp.prod_norm_sq_eq_of_L2 _

theorem spectralHarmonicRadialForget_smooth (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicRadialForget ell R (spectralHarmonicSmoothEmbedding ell R f)=
      spectralRadialSmoothEmbedding R f := by
  rfl

theorem spectralHarmonicAngularValue_smooth (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicAngularValue ell R (spectralHarmonicSmoothEmbedding ell R f)=
      ((Real.sqrt ((ell : ℝ)*(ell+10)) : ℝ) : ℂ) • spectralSmoothAngularValue R f := rfl

theorem spectralHarmonicVolume_compact (ell : ℕ) (R : ℝ) (hR : 0 < R) :
    IsCompactOperator ((spectralRadialValue R).comp (spectralHarmonicRadialForget ell R)) :=
  (spectralRadialValue_compact R hR).comp_clm _

end DefocusingNLS

end OAI
