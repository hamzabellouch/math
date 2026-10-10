import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSmoothCutoff

namespace OAI

/-! Smooth bounded cutoff multiplication preserves the completed harmonic H¹ domain. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralHarmonicJetMultiplier_smooth (ell : ℕ) (R : ℝ)
    (w d : SpectralHarmonicWeight R) (hw : w.density.HasTemperateGrowth)
    (hd : ∀ r, HasDerivAt w.density (d.density r) r) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicJetMultiplier R w d (spectralSmoothHarmonicJet ell R f)=
      spectralSmoothHarmonicJet ell R (spectralSmoothCutoff w.density f) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralRadialJetSpace R) (SpectralAngularL2 R)).injective
  apply Prod.ext
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralRadialL2 R) (SpectralRadialL2 R)).injective
    apply Prod.ext
    · change spectralL2ComplexMultiplier (radialPressureMeasure R) w.density
        w.radial_measurable w.bound w.radial_bound (spectralRadialSmoothValue R f)=
        spectralRadialSmoothValue R (spectralSmoothCutoff w.density f)
      exact spectralSmoothCutoff_L2 _ _ hw _ _ _ f
    · change spectralL2ComplexMultiplier (radialPressureMeasure R) d.density
        d.radial_measurable d.bound d.radial_bound (spectralRadialSmoothValue R f)+
        spectralL2ComplexMultiplier (radialPressureMeasure R) w.density
          w.radial_measurable w.bound w.radial_bound
            (spectralRadialSmoothValue R (SchwartzMap.derivCLM ℂ ℂ f))=
        spectralRadialSmoothValue R (SchwartzMap.derivCLM ℂ ℂ (spectralSmoothCutoff w.density f))
      apply Lp.ext
      filter_upwards [Lp.coeFn_add
          (spectralL2ComplexMultiplier (radialPressureMeasure R) d.density d.radial_measurable
            d.bound d.radial_bound (spectralRadialSmoothValue R f))
          (spectralL2ComplexMultiplier (radialPressureMeasure R) w.density w.radial_measurable
            w.bound w.radial_bound (spectralRadialSmoothValue R (SchwartzMap.derivCLM ℂ ℂ f))),
        spectralL2ComplexMultiplier_ae (radialPressureMeasure R) d.density
          d.radial_measurable d.bound d.radial_bound (spectralRadialSmoothValue R f),
        spectralL2ComplexMultiplier_ae (radialPressureMeasure R) w.density
          w.radial_measurable w.bound w.radial_bound
            (spectralRadialSmoothValue R (SchwartzMap.derivCLM ℂ ℂ f)),
        spectralRadialSmoothValue_ae R f,spectralRadialSmoothValue_ae R (SchwartzMap.derivCLM ℂ ℂ f),
        spectralRadialSmoothValue_ae R (SchwartzMap.derivCLM ℂ ℂ (spectralSmoothCutoff w.density f))]
          with r hadd hdv hwv hf hdf hcut
      rw [hadd,Pi.add_apply,hdv,hwv,hf,hdf,hcut]
      simpa only [Complex.real_smul] using (spectralSmoothCutoff_derivative w.density d.density hw hd f r).symm
  · change spectralL2ComplexMultiplier (spectralAngularMeasure R) w.density
      w.angular_measurable w.bound w.angular_bound
        ((Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ) • spectralSmoothAngularValue R f)=
      (Real.sqrt ((ell : ℝ)*(ell+10)) : ℂ) •
        spectralSmoothAngularValue R (spectralSmoothCutoff w.density f)
    rw [map_smul]
    congr 1
    exact spectralSmoothCutoff_L2 _ _ hw _ _ _ f

theorem spectralHarmonicJetMultiplier_mem (ell : ℕ) (R : ℝ)
    (w d : SpectralHarmonicWeight R) (hw : w.density.HasTemperateGrowth)
    (hd : ∀ r, HasDerivAt w.density (d.density r) r) (u : SpectralHarmonicEnergy ell R) :
    spectralHarmonicJetMultiplier R w d u ∈ spectralHarmonicSubspace ell R := by
  let K := spectralHarmonicJetMultiplier R w d
  let S := spectralHarmonicSubspace ell R
  have hr : LinearMap.range (spectralSmoothHarmonicJet ell R).toLinearMap ≤
      S.comap K.toLinearMap := by
    rintro _ ⟨f,rfl⟩
    change spectralHarmonicJetMultiplier R w d (spectralSmoothHarmonicJet ell R f) ∈ S
    rw [spectralHarmonicJetMultiplier_smooth ell R w d hw hd f]
    exact (LinearMap.range (spectralSmoothHarmonicJet ell R).toLinearMap).le_topologicalClosure
      ⟨spectralSmoothCutoff w.density f,rfl⟩
  have hc : IsClosed ((S.comap K.toLinearMap : Submodule ℂ (SpectralHarmonicJet R)) :
      Set (SpectralHarmonicJet R)) :=
    (LinearMap.range (spectralSmoothHarmonicJet ell R).toLinearMap).isClosed_topologicalClosure.preimage K.continuous
  exact (LinearMap.range (spectralSmoothHarmonicJet ell R).toLinearMap).topologicalClosure_minimal hr hc u.property

noncomputable def spectralHarmonicMultiplier (ell : ℕ) (R : ℝ)
    (w d : SpectralHarmonicWeight R) (hw : w.density.HasTemperateGrowth)
    (hd : ∀ r, HasDerivAt w.density (d.density r) r) :
    SpectralHarmonicEnergy ell R →L[ℂ] SpectralHarmonicEnergy ell R :=
  ((spectralHarmonicJetMultiplier R w d).comp (spectralHarmonicSubspace ell R).subtypeL).codRestrict
    (spectralHarmonicSubspace ell R) (spectralHarmonicJetMultiplier_mem ell R w d hw hd)

end DefocusingNLS

end OAI
