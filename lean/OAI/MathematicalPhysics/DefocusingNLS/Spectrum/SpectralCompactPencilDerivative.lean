import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilDerivative

namespace OAI

/-! Parameter derivatives of finite-power compact pencils. -/

namespace DefocusingNLS.SpectralPenaltyFamily
variable {R l : ℝ}

noncomputable local instance compactDerivativeCoefficientNormed (ell : ℕ) (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance compactDerivativePencilNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem compactPencil_hasDerivAt (s : SpectralPenaltyFamily R l) (ell n : ℕ)
    (hR : 0 < R)
    (K : ℂ → SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (D : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (ζ : ℂ) (hK : HasDerivAt K D ζ) :
    HasDerivAt (fun z => s.compactPencil ell hR n (K z))
      (s.compactPencil ell hR n D) ζ := by
  let L := ContinuousLinearMap.compL ℂ (SpectralRadialObservationSpace R)
    (SpectralHarmonicPair ell R) (SpectralRadialObservationSpace R)
      (s.observedComplexInverse ell hR n)
  exact L.hasFDerivAt.comp_hasDerivAt ζ hK

end DefocusingNLS.SpectralPenaltyFamily

end OAI
