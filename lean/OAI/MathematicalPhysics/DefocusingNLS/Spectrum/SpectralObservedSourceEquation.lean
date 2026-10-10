import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalPairing

namespace OAI

/-! Inhomogeneous smooth tests determine the actual observed inverse and pencil chain. -/

open scoped SchwartzMap
namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

theorem observedComplexInverse_of_complex_tests (s : SpectralPenaltyFamily R l)
    (ell n : ℕ) (hR : 0 < R) (load u : SpectralHarmonicPair ell R)
    (hf : ∀ φ : 𝓢(ℝ,ℂ), star (s.penaltyComplexForm ell n u (spectralFirstTest ell R φ))=
      inner ℂ (spectralFirstTest ell R φ) load)
    (hg : ∀ φ : 𝓢(ℝ,ℂ), star (s.penaltyComplexForm ell n u (spectralSecondTest ell R φ))=
      inner ℂ (spectralSecondTest ell R φ) load) :
    s.observedComplexInverse ell hR n load=spectralHarmonicObservation ell R hR u := by
  let F := InnerProductSpace.toDual ℝ (SpectralHarmonicPair ell R) load
  have he : s.penaltyForm ell n u=F := by
    apply spectralPairFunctional_ext ell R
    · intro φ
      change _ = inner ℝ load (spectralFirstTest ell R φ)
      have h := congrArg Complex.re (hf φ)
      simpa only [Complex.star_def,Complex.conj_re,penaltyComplexForm_re,
        spectralHarmonicPairInner_re,real_inner_comm] using h
    · intro φ
      change _ = inner ℝ load (spectralSecondTest ell R φ)
      have h := congrArg Complex.re (hg φ)
      simpa only [Complex.star_def,Complex.conj_re,penaltyComplexForm_re,
        spectralHarmonicPairInner_re,real_inner_comm] using h
  have hu := s.inverse_unique ell n F u (fun v => DFunLike.congr_fun he v)
  rw [s.observedComplexInverse_apply]
  change spectralHarmonicObservation ell R hR (s.inverse ell n F)=_
  rw [← hu]

theorem compactPencil_source_of_complex_tests (s : SpectralPenaltyFamily R l)
    (ell n : ℕ) (hR : 0 < R)
    (K D : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (u v : SpectralHarmonicPair ell R)
    (hf : ∀ φ : 𝓢(ℝ,ℂ), star (s.penaltyComplexForm ell n u (spectralFirstTest ell R φ))=
      inner ℂ (spectralFirstTest ell R φ)
        (K (spectralHarmonicObservation ell R hR u)+D (spectralHarmonicObservation ell R hR v)))
    (hg : ∀ φ : 𝓢(ℝ,ℂ), star (s.penaltyComplexForm ell n u (spectralSecondTest ell R φ))=
      inner ℂ (spectralSecondTest ell R φ)
        (K (spectralHarmonicObservation ell R hR u)+D (spectralHarmonicObservation ell R hR v))) :
    spectralHarmonicObservation ell R hR u-
      s.compactPencil ell hR n K (spectralHarmonicObservation ell R hR u)=
      s.compactPencil ell hR n D (spectralHarmonicObservation ell R hR v) := by
  have h := s.observedComplexInverse_of_complex_tests ell n hR _ u hf hg
  rw [map_add] at h
  change s.compactPencil ell hR n K (spectralHarmonicObservation ell R hR u)+
    s.compactPencil ell hR n D (spectralHarmonicObservation ell R hR v)=
      spectralHarmonicObservation ell R hR u at h
  exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))

end DefocusingNLS.SpectralPenaltyFamily

end OAI
