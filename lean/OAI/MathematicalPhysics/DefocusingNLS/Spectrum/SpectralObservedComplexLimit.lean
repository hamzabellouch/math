import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPenaltyComplex
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPenaltyNormLimit

namespace OAI

/-! Complex observation operators for the compact-pencil construction. -/

open Set Filter Topology InnerProductSpace
namespace DefocusingNLS

noncomputable def spectralComplexLimit
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    (T : ℕ → E →L[ℂ] F) (T₀ : E →L[ℝ] F)
    (hT : ∀ u, Tendsto (fun n => T n u) atTop (𝓝 (T₀ u))) : E →L[ℂ] F where
  toFun := T₀
  map_add' := T₀.map_add
  map_smul' := by
    intro c u
    apply tendsto_nhds_unique (hT (c • u))
    simpa only [map_smul,RingHom.id_apply] using (hT u).const_smul c
  cont := T₀.continuous

noncomputable def spectralRealRiesz (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] : E →L[ℝ] StrongDual ℝ E :=
  (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap

theorem spectralRieszObservation_tendsto {E Z : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : ℕ → StrongDual ℝ E →L[ℝ] Z) (T₀ : StrongDual ℝ E →L[ℝ] Z)
    (hT : Tendsto T atTop (𝓝 T₀)) :
    Tendsto (fun n => (T n).comp (spectralRealRiesz E))
      atTop (𝓝 (T₀.comp (spectralRealRiesz E))) := by
  exact ((ContinuousLinearMap.compL ℝ E (StrongDual ℝ E) Z).continuous₂.continuousAt.tendsto).comp
    (hT.prodMk_nhds tendsto_const_nhds)

theorem spectralRieszObservation_pointwise {E Z : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : ℕ → StrongDual ℝ E →L[ℝ] Z) (T₀ : StrongDual ℝ E →L[ℝ] Z)
    (hT : Tendsto T atTop (𝓝 T₀)) (u : E) :
    Tendsto (fun n => T n (toDual ℝ E u)) atTop (𝓝 (T₀ (toDual ℝ E u))) :=
  (ContinuousLinearMap.apply ℝ Z (toDual ℝ E u)).continuous.continuousAt.tendsto.comp hT

namespace SpectralPenaltyFamily
variable {R l : ℝ}

noncomputable def observedComplexInverse (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hR : 0 < R) (n : ℕ) : SpectralHarmonicPair ell R →L[ℂ] SpectralRadialObservationSpace R :=
  (spectralHarmonicObservation ell R hR).comp
    (spectralHarmonicPenaltyInverseComplex ell R (s.weight n) s.lower s.lower_pos
      (s.radial_lower n) (s.angular_lower n) (s.pressure n) (s.pressure_measurable n)
      (s.pressure_bound n) (s.pressure_nonneg n) (s.scale n) (s.scale_pos n))

noncomputable def observedRieszLimit (s : SpectralPenaltyFamily R l) (ell : ℕ) (hR : 0 < R) :
    SpectralHarmonicPair ell R →L[ℝ] SpectralRadialObservationSpace R :=
  (s.observedLimitInverse ell hR).comp
    (spectralRealRiesz (SpectralHarmonicPair ell R))

theorem observedComplexInverse_apply (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hR : 0 < R) (n : ℕ) (u : SpectralHarmonicPair ell R) :
    s.observedComplexInverse ell hR n u =
      s.observedInverse ell hR n (toDual ℝ (SpectralHarmonicPair ell R) u) := rfl

theorem observedComplexInverse_pointwise (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R) (u : SpectralHarmonicPair ell R) :
    Tendsto (fun n => s.observedComplexInverse ell (hl.trans hlR) n u) atTop
      (𝓝 (s.observedRieszLimit ell (hl.trans hlR) u)) := by
  exact spectralRieszObservation_pointwise (E := SpectralHarmonicPair ell R)
    (Z := SpectralRadialObservationSpace R) _ _ (s.observedInverse_tendsto ell hl hlR) u

noncomputable def observedComplexLimit (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R) : SpectralHarmonicPair ell R →L[ℂ] SpectralRadialObservationSpace R :=
  spectralComplexLimit (E := SpectralHarmonicPair ell R)
    (F := SpectralRadialObservationSpace R) (s.observedComplexInverse ell (hl.trans hlR))
    (s.observedRieszLimit ell (hl.trans hlR)) (s.observedComplexInverse_pointwise ell hl hlR)

theorem observedComplexInverse_tendsto (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R) :
    Tendsto (s.observedComplexInverse ell (hl.trans hlR)) atTop
      (𝓝 (s.observedComplexLimit ell hl hlR)) := by
  have h := spectralRieszObservation_tendsto (E := SpectralHarmonicPair ell R)
    (Z := SpectralRadialObservationSpace R) _ _ (s.observedInverse_tendsto ell hl hlR)
  let A := ContinuousLinearMap.restrictScalarsIsometry ℂ
    (SpectralHarmonicPair ell R) (SpectralRadialObservationSpace R) ℝ ℝ
  apply A.isometry.tendsto_nhds_iff.mpr
  exact h

end SpectralPenaltyFamily
end DefocusingNLS

end OAI
