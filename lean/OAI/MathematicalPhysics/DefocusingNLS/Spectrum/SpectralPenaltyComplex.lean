import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPenaltyFamily
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicPhase

namespace OAI

/-! Complex linearity of the pressure inverse on Riesz-represented loads. -/

open MeasureTheory
namespace DefocusingNLS

theorem spectralHarmonicPenaltyForm_I (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1) (a : ℝ)
    (u v : SpectralHarmonicPair ell R) :
    spectralCoercivePenaltyForm (spectralHarmonicPairForm ell R w)
      (spectralHarmonicFirstValue ell R) (spectralWeightedPressure R w p hpm hpb) a
        (Complex.I • u) v =
    -spectralCoercivePenaltyForm (spectralHarmonicPairForm ell R w)
      (spectralHarmonicFirstValue ell R) (spectralWeightedPressure R w p hpm hpb) a
        u (Complex.I • v) := by
  let V := ((spectralRadialValue R).comp (spectralHarmonicRadialForget ell R)).comp
    (WithLp.fstL 2 ℂ (SpectralHarmonicEnergy ell R) (SpectralHarmonicEnergy ell R))
  let P := spectralL2ComplexMultiplier (radialPressureMeasure R)
    (fun r => w.density r*p r) (w.radial_measurable.mul hpm) w.bound
    (weightedPressure_bound R w p hpb)
  change spectralHarmonicPairForm ell R w (Complex.I • u) v+
      a⁻¹*inner ℝ (P (V (Complex.I • u))) (V v)=
    -(spectralHarmonicPairForm ell R w u (Complex.I • v)+
      a⁻¹*inner ℝ (P (V u)) (V (Complex.I • v)))
  simp only [spectralHarmonicPairForm_I,map_smul,spectralCompatibleInner_I]
  ring

noncomputable def spectralHarmonicPenaltyInverseComplex (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hpn : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ p r) (a : ℝ) (ha : 0 < a) :
    SpectralHarmonicPair ell R →L[ℂ] SpectralHarmonicPair ell R :=
  by
  let B := spectralCoercivePenaltyForm (spectralHarmonicPairForm ell R w)
    (spectralHarmonicFirstValue ell R) (spectralWeightedPressure R w p hpm hpb) a
  have hP := spectralWeightedPressure_nonneg R w
    (hcr.mono (fun _ h => hc.le.trans h)) p hpm hpb hpn
  have hB : IsCoercive B := spectralCoercivePenaltyForm_coercive
    (spectralHarmonicPairForm ell R w) c hc
    (spectralHarmonicPairForm_lower ell R w c hcr hca)
    (spectralHarmonicFirstValue ell R) (spectralWeightedPressure R w p hpm hpb) hP a ha
  exact spectralHermitianInverse (E := SpectralHarmonicPair ell R) B hB
    (spectralHarmonicPenaltyForm_I ell R w p hpm hpb a)

theorem spectralHarmonicPenaltyInverseComplex_apply (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hpn : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ p r) (a : ℝ) (ha : 0 < a)
    (f : SpectralHarmonicPair ell R) :
    spectralHarmonicPenaltyInverseComplex ell R w c hc hcr hca p hpm hpb hpn a ha f =
      spectralHarmonicPenaltyInverse ell R w c hc hcr hca p hpm hpb hpn a ha
        (InnerProductSpace.toDual ℝ (SpectralHarmonicPair ell R) f) := rfl

end DefocusingNLS

end OAI
