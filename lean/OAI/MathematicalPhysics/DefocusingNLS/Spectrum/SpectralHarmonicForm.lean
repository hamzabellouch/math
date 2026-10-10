import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicObservation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2Multiplier
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoerciveInverse

namespace OAI

/-! The weighted base form, including the harmonic angular derivative. -/

open MeasureTheory InnerProductSpace
namespace DefocusingNLS

structure SpectralHarmonicWeight (R : ℝ) where
  density : ℝ → ℝ
  bound : ℝ
  radial_measurable : AEStronglyMeasurable density (radialPressureMeasure R)
  angular_measurable : AEStronglyMeasurable density (spectralAngularMeasure R)
  radial_bound : ∀ᵐ r ∂radialPressureMeasure R, ‖density r‖ ≤ bound
  angular_bound : ∀ᵐ r ∂spectralAngularMeasure R, ‖density r‖ ≤ bound

noncomputable def spectralHarmonicValue (ell : ℕ) (R : ℝ) :
    SpectralHarmonicEnergy ell R →L[ℝ] SpectralRadialL2 R :=
  ((spectralRadialValue R).comp (spectralHarmonicRadialForget ell R)).restrictScalars ℝ

noncomputable def spectralHarmonicDerivative (ell : ℕ) (R : ℝ) :
    SpectralHarmonicEnergy ell R →L[ℝ] SpectralRadialL2 R :=
  ((spectralRadialDerivative R).comp (spectralHarmonicRadialForget ell R)).restrictScalars ℝ

noncomputable def spectralHarmonicForm (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R) :
    SpectralHarmonicEnergy ell R →L[ℝ] SpectralHarmonicEnergy ell R →L[ℝ] ℝ :=
  let P := spectralL2Multiplier (radialPressureMeasure R) w.density w.radial_measurable
    w.bound w.radial_bound
  let A := spectralL2Multiplier (spectralAngularMeasure R) w.density w.angular_measurable
    w.bound w.angular_bound
  let V := spectralHarmonicValue ell R
  let D := spectralHarmonicDerivative ell R
  let G := (spectralHarmonicAngularValue ell R).restrictScalars ℝ
  (innerSL ℝ).bilinearComp (P.comp V) V +
    (innerSL ℝ).bilinearComp (P.comp D) D + (innerSL ℝ).bilinearComp (A.comp G) G

theorem spectralHarmonicForm_lower (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R)
    (c : ℝ) (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (u : SpectralHarmonicEnergy ell R) : c*‖u‖^2 ≤ spectralHarmonicForm ell R w u u := by
  have hv := spectralL2Multiplier_lower (radialPressureMeasure R) w.density
    w.radial_measurable w.bound w.radial_bound c hcr (spectralHarmonicValue ell R u)
  have hd := spectralL2Multiplier_lower (radialPressureMeasure R) w.density
    w.radial_measurable w.bound w.radial_bound c hcr (spectralHarmonicDerivative ell R u)
  have ha := spectralL2Multiplier_lower (spectralAngularMeasure R) w.density
    w.angular_measurable w.bound w.angular_bound c hca (spectralHarmonicAngularValue ell R u)
  rw [spectralHarmonicEnergy_norm_sq,spectralRadialEnergy_norm_sq]
  let P := spectralL2Multiplier (radialPressureMeasure R) w.density
    w.radial_measurable w.bound w.radial_bound
  let A := spectralL2Multiplier (spectralAngularMeasure R) w.density
    w.angular_measurable w.bound w.angular_bound
  change _ ≤ inner ℝ (P (spectralHarmonicValue ell R u)) (spectralHarmonicValue ell R u)+
    inner ℝ (P (spectralHarmonicDerivative ell R u)) (spectralHarmonicDerivative ell R u)+
    inner ℝ (A (spectralHarmonicAngularValue ell R u)) (spectralHarmonicAngularValue ell R u)
  change c*‖spectralRadialValue R (spectralHarmonicRadialForget ell R u)‖^2 ≤ _ at hv
  change c*‖spectralRadialDerivative R (spectralHarmonicRadialForget ell R u)‖^2 ≤ _ at hd
  nlinarith

noncomputable def spectralHarmonicPairForm (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R) :
    SpectralHarmonicPair ell R →L[ℝ] SpectralHarmonicPair ell R →L[ℝ] ℝ :=
  let F := (WithLp.fstL 2 ℂ (SpectralHarmonicEnergy ell R)
    (SpectralHarmonicEnergy ell R)).restrictScalars ℝ
  let S := (WithLp.sndL 2 ℂ (SpectralHarmonicEnergy ell R)
    (SpectralHarmonicEnergy ell R)).restrictScalars ℝ
  (spectralHarmonicForm ell R w).bilinearComp F F +
    (spectralHarmonicForm ell R w).bilinearComp S S

theorem spectralHarmonicPairForm_lower (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R)
    (c : ℝ) (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r)
    (u : SpectralHarmonicPair ell R) : c*‖u‖^2 ≤ spectralHarmonicPairForm ell R w u u := by
  have hf := spectralHarmonicForm_lower ell R w c hcr hca u.fst
  have hs := spectralHarmonicForm_lower ell R w c hcr hca u.snd
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change _ ≤ spectralHarmonicForm ell R w u.fst u.fst+spectralHarmonicForm ell R w u.snd u.snd
  nlinarith

theorem spectralHarmonicPairForm_coercive (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R)
    (c : ℝ) (hc : 0 < c) (hcr : ∀ᵐ r ∂radialPressureMeasure R, c ≤ w.density r)
    (hca : ∀ᵐ r ∂spectralAngularMeasure R, c ≤ w.density r) :
    IsCoercive (spectralHarmonicPairForm ell R w) := by
  refine ⟨c,hc,fun u => ?_⟩
  simpa only [pow_two,mul_assoc] using spectralHarmonicPairForm_lower ell R w c hcr hca u

end DefocusingNLS

end OAI
