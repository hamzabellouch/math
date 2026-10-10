import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicForm
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoercivePenalty

namespace OAI

/-! The pressure-penalized inverse for the weighted harmonic pair form. -/

open MeasureTheory InnerProductSpace
namespace DefocusingNLS

theorem weightedPressure_bound (R : ℝ) (w : SpectralHarmonicWeight R)
    (p : ℝ → ℝ) (hp : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1) :
    ∀ᵐ r ∂radialPressureMeasure R, ‖w.density r*p r‖ ≤ w.bound := by
  filter_upwards [hp,w.radial_bound] with r hr hw
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hr).trans hw

noncomputable def spectralWeightedPressure (R : ℝ) (w : SpectralHarmonicWeight R)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1) :
    SpectralRadialL2 R →L[ℝ] SpectralRadialL2 R :=
  spectralL2Multiplier (radialPressureMeasure R) (fun r => w.density r*p r)
    (w.radial_measurable.mul hpm) w.bound (weightedPressure_bound R w p hpb)

theorem spectralWeightedPressure_nonneg (R : ℝ) (w : SpectralHarmonicWeight R)
    (hw : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ w.density r)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hpn : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ p r) (u : SpectralRadialL2 R) :
    0 ≤ inner ℝ (spectralWeightedPressure R w p hpm hpb u) u := by
  have hn : ∀ᵐ r ∂radialPressureMeasure R, (0 : ℝ) ≤ w.density r*p r := by
    filter_upwards [hw,hpn] with r hwr hpr
    exact mul_nonneg hwr hpr
  simpa only [zero_mul,spectralWeightedPressure] using spectralL2Multiplier_lower (radialPressureMeasure R)
    (fun r => w.density r*p r) (w.radial_measurable.mul hpm) w.bound
    (weightedPressure_bound R w p hpb) 0 hn u

noncomputable def spectralHarmonicPenaltyInverse (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hpn : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ p r) (a : ℝ) (ha : 0 < a) :
    StrongDual ℝ (SpectralHarmonicPair ell R) →L[ℝ] SpectralHarmonicPair ell R :=
  spectralCoercivePenaltyInverse (spectralHarmonicPairForm ell R w) c hc
    (spectralHarmonicPairForm_lower ell R w c hcr hca) (spectralHarmonicFirstValue ell R)
    (spectralWeightedPressure R w p hpm hpb)
    (spectralWeightedPressure_nonneg R w (hcr.mono (fun _ hr => hc.le.trans hr)) p hpm hpb hpn) a ha

theorem spectralHarmonicPenaltyInverse_norm (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hpn : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ p r) (a : ℝ) (ha : 0 < a)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) :
    ‖spectralHarmonicPenaltyInverse ell R w c hc hcr hca p hpm hpb hpn a ha F‖ ≤ ‖F‖/c :=
  spectralCoercivePenaltyInverse_norm _ _ _ _ _ _ _ _ _ _

theorem spectralHarmonicPenaltyInverse_energy (ell : ℕ) (R : ℝ)
    (w : SpectralHarmonicWeight R) (c : ℝ) (hc : 0 < c)
    (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (p : ℝ → ℝ) (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (hpn : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ p r) (a : ℝ) (ha : 0 < a)
    (F : StrongDual ℝ (SpectralHarmonicPair ell R)) :
    let u := spectralHarmonicFirstValue ell R
      (spectralHarmonicPenaltyInverse ell R w c hc hcr hca p hpm hpb hpn a ha F)
    (∫ r, w.density r*p r*‖u r‖^2 ∂radialPressureMeasure R) ≤ a*‖F‖^2/c := by
  intro u
  have he := spectralCoercivePenaltyInverse_energy (spectralHarmonicPairForm ell R w) c hc
    (spectralHarmonicPairForm_lower ell R w c hcr hca) (spectralHarmonicFirstValue ell R)
    (spectralWeightedPressure R w p hpm hpb)
    (spectralWeightedPressure_nonneg R w (hcr.mono (fun _ hr => hc.le.trans hr)) p hpm hpb hpn) a ha F
  change inner ℝ (spectralWeightedPressure R w p hpm hpb u) u ≤ _ at he
  rw [spectralWeightedPressure,spectralL2Multiplier_quadratic] at he
  exact he

end DefocusingNLS

end OAI
