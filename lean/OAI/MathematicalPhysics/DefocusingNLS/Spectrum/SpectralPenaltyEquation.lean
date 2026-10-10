import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicPenalty

namespace OAI

/-! Exact variational equation of the weighted pressure-penalized inverse. -/

open MeasureTheory InnerProductSpace
namespace DefocusingNLS

theorem spectralHarmonicPenaltyInverse_equation (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hpn : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ p r) (a : ℝ) (ha : 0 < a)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) (v : SpectralHarmonicPair ell R) :
    let u := spectralHarmonicPenaltyInverse ell R w c hc hcr hca p hpm hpb hpn a ha F
    spectralHarmonicPairForm ell R w u v+
      a⁻¹*inner ℝ (spectralWeightedPressure R w p hpm hpb (spectralHarmonicFirstValue ell R u))
        (spectralHarmonicFirstValue ell R v)=F v := by
  exact spectralCoerciveInverse_equation
    (spectralCoercivePenaltyForm (spectralHarmonicPairForm ell R w)
      (spectralHarmonicFirstValue ell R) (spectralWeightedPressure R w p hpm hpb) a)
    (spectralCoercivePenaltyForm_coercive (spectralHarmonicPairForm ell R w) c hc
      (spectralHarmonicPairForm_lower ell R w c hcr hca) (spectralHarmonicFirstValue ell R)
      (spectralWeightedPressure R w p hpm hpb)
      (spectralWeightedPressure_nonneg R w (hcr.mono (fun _ hr => hc.le.trans hr)) p hpm hpb hpn)
      a ha) F v

end DefocusingNLS

end OAI
