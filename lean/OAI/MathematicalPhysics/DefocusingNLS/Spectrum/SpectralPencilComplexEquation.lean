import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilVariational
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicComplexForm

namespace OAI

/-! The limiting compact-pencil equation supplies the full complex weak equation. -/

open MeasureTheory
namespace DefocusingNLS

theorem spectralHarmonicCore_smul_mem (ell : ℕ) (R l : ℝ)
    (u : SpectralHarmonicPair ell R) (hu : u ∈ spectralHarmonicCoreSubspace ell R l)
    (c : ℂ) : c • u ∈ spectralHarmonicCoreSubspace ell R l := by
  rw [spectralHarmonicCore_mem] at hu ⊢
  let V : SpectralHarmonicPair ell R →L[ℂ] SpectralRadialL2 R :=
    ((spectralRadialValue R).comp (spectralHarmonicRadialForget ell R)).comp
      (WithLp.fstL 2 ℂ (SpectralHarmonicEnergy ell R) (SpectralHarmonicEnergy ell R))
  change (fun r => V (c • u) r) =ᵐ[(radialPressureMeasure R).restrict (Set.Iic l)] 0
  rw [map_smul]
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c (V u)),hu] with r hs hr
  rw [hs,Pi.smul_apply]
  change V u r=0 at hr
  rw [hr,smul_zero]
  rfl

namespace SpectralPenaltyFamily
variable {R l : ℝ}

theorem limitPencil_complex_variational (s : SpectralPenaltyFamily R l) (ell : ℕ)
    (hl : 0 < l) (hlR : l < R)
    (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (z : SpectralRadialObservationSpace R) :
    s.limitPencil ell hl hlR K z=z ↔
      ∃ u : SpectralHarmonicPair ell R, u ∈ spectralHarmonicCoreSubspace ell R l ∧
        spectralHarmonicObservation ell R (hl.trans hlR) u=z ∧
        ∀ v : SpectralHarmonicCore ell R l,
          spectralHarmonicPairComplexForm ell R s.limitWeight u v=inner ℂ (K z) v := by
  rw [s.limitPencil_variational ell hl hlR K z]
  constructor
  · rintro ⟨u,hu,hobs,hweak⟩
    refine ⟨u,hu,hobs,fun v => ?_⟩
    apply spectralHarmonicPairComplexForm_of_real
    · exact hweak v
    · exact hweak ⟨Complex.I • (v : SpectralHarmonicPair ell R),
        spectralHarmonicCore_smul_mem ell R l v v.property Complex.I⟩
  · rintro ⟨u,hu,hobs,hweak⟩
    refine ⟨u,hu,hobs,fun v => ?_⟩
    have h := congrArg Complex.re (hweak v)
    simpa only [spectralHarmonicPairComplexForm_re,spectralHarmonicPairInner_re] using h

end SpectralPenaltyFamily
end DefocusingNLS

end OAI
