import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialVolumeCompact
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCoreSpace

namespace OAI

/-! Compact volume-plus-boundary observation in a fixed spherical harmonic. -/

namespace DefocusingNLS

private theorem compact_pair {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : E →L[ℂ] F) (g : E →L[ℂ] G) (hf : IsCompactOperator f) (hg : IsCompactOperator g) :
    IsCompactOperator (f.prod g) := by
  have h₁ := hf.clm_comp (ContinuousLinearMap.inl ℂ F G)
  have h₂ := hg.clm_comp (ContinuousLinearMap.inr ℂ F G)
  convert h₁.add h₂ using 1
  funext x
  simp only [Function.comp_apply,Pi.add_apply,ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply,ContinuousLinearMap.prod_apply,Prod.mk_add_mk,add_zero,zero_add]

noncomputable abbrev SpectralRadialObservationSpace (R : ℝ) :=
  (SpectralRadialL2 R × SpectralRadialL2 R) × (ℂ × ℂ)

noncomputable def spectralRadialPairValue (R : ℝ) :
    SpectralRadialPairEnergy R →L[ℂ] SpectralRadialL2 R × SpectralRadialL2 R :=
  ((spectralRadialValue R).comp
    (WithLp.fstL 2 ℂ (SpectralRadialEnergy R) (SpectralRadialEnergy R))).prod
  ((spectralRadialValue R).comp
    (WithLp.sndL 2 ℂ (SpectralRadialEnergy R) (SpectralRadialEnergy R)))

theorem spectralRadialPairValue_compact (R : ℝ) (hR : 0 < R) :
    IsCompactOperator (spectralRadialPairValue R) := by
  exact compact_pair _ _
    ((spectralRadialValue_compact R hR).comp_clm
      (WithLp.fstL 2 ℂ (SpectralRadialEnergy R) (SpectralRadialEnergy R)))
    ((spectralRadialValue_compact R hR).comp_clm
      (WithLp.sndL 2 ℂ (SpectralRadialEnergy R) (SpectralRadialEnergy R)))

noncomputable def spectralRadialObservation (R : ℝ) (hR : 0 < R) :
    SpectralRadialPairEnergy R →L[ℂ] SpectralRadialObservationSpace R :=
  (spectralRadialPairValue R).prod (spectralRadialPairTrace R hR)

theorem spectralRadialObservation_compact (R : ℝ) (hR : 0 < R) :
    IsCompactOperator (spectralRadialObservation R hR) :=
  compact_pair _ _ (spectralRadialPairValue_compact R hR) (spectralRadialPairTrace_compact R hR)

end DefocusingNLS

end OAI
