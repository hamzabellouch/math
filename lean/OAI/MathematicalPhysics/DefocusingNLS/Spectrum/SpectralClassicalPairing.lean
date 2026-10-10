import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicScalarPairing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSmoothPairTesting
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralObservationZero

namespace OAI

/-! Classical representatives and their exact completed-space test pairings. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralHarmonicValue_classical_ae (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : SpectralHarmonicEnergy ell R) (f : ℝ → ℂ)
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u r=f r) :
    spectralHarmonicValue ell R u =ᵐ[radialPressureMeasure R] f := by
  filter_upwards [spectralRadialRepresentative_ae R hR (spectralHarmonicRadialForget ell R u),
    radialPressureMeasure_ae_positive R] with r he hr
  exact he.symm.trans (hf r hr)

theorem spectralHarmonicScalar_classical_pairing (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicEnergy ell R) (f : ℝ → ℂ)
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u r=f r)
    (hd : spectralHarmonicDerivative ell R u =ᵐ[radialPressureMeasure R] deriv f)
    (φ : 𝓢(ℝ,ℂ)) :
    star (spectralHarmonicComplexForm ell R w u (spectralHarmonicSmoothEmbedding ell R φ))=
      (∫ r, star (φ r)*(w.density r • f r) ∂radialPressureMeasure R)+
      (∫ r, star (deriv φ r)*(w.density r • deriv f r) ∂radialPressureMeasure R)+
      (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
        (∫ r, star (φ r)*(w.density r • f r) ∂spectralAngularMeasure R) := by
  rw [spectralHarmonicScalar_pairing]
  have hv := spectralHarmonicValue_classical_ae ell R hR u f hf
  have ha := (spectralAngularMeasure_absolutelyContinuous R).ae_le hv
  have hvI : (∫ r, star (φ r)*(w.density r • spectralHarmonicValue ell R u r)
      ∂radialPressureMeasure R)=(∫ r, star (φ r)*(w.density r • f r) ∂radialPressureMeasure R) := by
    apply integral_congr_ae
    filter_upwards [hv] with r hr
    rw [hr]
  have hdI : (∫ r, star (deriv φ r)*(w.density r • spectralHarmonicDerivative ell R u r)
      ∂radialPressureMeasure R)=(∫ r, star (deriv φ r)*(w.density r • deriv f r) ∂radialPressureMeasure R) := by
    apply integral_congr_ae
    filter_upwards [hd] with r hr
    rw [hr]
  have haI : (∫ r, star (φ r)*(w.density r • spectralHarmonicValue ell R u r)
      ∂spectralAngularMeasure R)=(∫ r, star (φ r)*(w.density r • f r) ∂spectralAngularMeasure R) := by
    apply integral_congr_ae
    filter_upwards [ha] with r hr
    rw [hr]
  rw [hvI,hdI,haI]

theorem spectralPressure_classical_pairing (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (p : ℝ → ℝ)
    (hpm : AEStronglyMeasurable p (radialPressureMeasure R))
    (hpb : ∀ᵐ r ∂radialPressureMeasure R, ‖p r‖ ≤ 1)
    (u : SpectralHarmonicEnergy ell R) (f : ℝ → ℂ)
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u r=f r)
    (φ : 𝓢(ℝ,ℂ)) :
    inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R φ))
      (spectralWeightedPressure R w p hpm hpb (spectralHarmonicValue ell R u))=
        ∫ r, star (φ r)*((w.density r*p r) • f r) ∂radialPressureMeasure R := by
  have he := spectralL2ComplexMultiplier_pairing_test (radialPressureMeasure R)
    (fun r => w.density r*p r) (w.radial_measurable.mul hpm) w.bound
    (weightedPressure_bound R w p hpb) (spectralHarmonicValue ell R u)
    (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R φ))
    φ (spectralHarmonicValue_smooth_ae ell R φ)
  change inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R φ))
    (spectralWeightedPressure R w p hpm hpb (spectralHarmonicValue ell R u))=_ at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [spectralHarmonicValue_classical_ae ell R hR u f hf] with r hr
  rw [hr]

theorem spectralHarmonicClassical_zero_of_value (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : SpectralHarmonicEnergy ell R) (f : ℝ → ℂ) (hfc : ContinuousOn f (Icc 0 R))
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u r=f r)
    (hu : spectralHarmonicValue ell R u=0) : ∀ r ∈ Icc 0 R, f r=0 := by
  have hzero : spectralHarmonicValue ell R u =ᵐ[radialPressureMeasure R] (0 : ℝ → ℂ) := by
    rw [hu]
    exact Lp.coeFn_zero ℂ 2 (radialPressureMeasure R)
  have hv := (spectralHarmonicValue_classical_ae ell R hR u f hf).symm.trans hzero
  exact Measure.eqOn_Icc_of_ae_eq volume hR.ne
    ((spectralRadialVolume_absolutelyContinuous R).ae_le hv) hfc continuousOn_const

theorem spectralObservation_ne_zero_of_classical (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : SpectralHarmonicPair ell R) (f g : ℝ → ℂ)
    (hfc : ContinuousOn f (Icc 0 R)) (hgc : ContinuousOn g (Icc 0 R))
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hg : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (hne : ∃ r ∈ Icc 0 R, f r ≠ 0 ∨ g r ≠ 0) :
    spectralHarmonicObservation ell R hR u ≠ 0 := by
  intro hz
  rw [spectralHarmonicObservation_coordinates] at hz
  have huf : spectralHarmonicValue ell R u.fst=0 := congrArg (fun v => v.1.1) hz
  have hug : spectralHarmonicValue ell R u.snd=0 := congrArg (fun v => v.1.2) hz
  obtain ⟨r,hr,hfne | hgne⟩ := hne
  · exact hfne (spectralHarmonicClassical_zero_of_value ell R hR u.fst f hfc hf huf r hr)
  · exact hgne (spectralHarmonicClassical_zero_of_value ell R hR u.snd g hgc hg hug r hr)

private theorem realPart_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [InnerProductSpace ℝ E] (u v : E) :
    (inner ℂ u v).re=inner ℝ u v :=
  (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) u v).trans
    (real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two u v).symm

namespace SpectralPenaltyFamily
variable {R l : ℝ}

noncomputable def penaltyComplexForm (s : SpectralPenaltyFamily R l) (ell n : ℕ)
    (u v : SpectralHarmonicPair ell R) : ℂ :=
  spectralHarmonicPairComplexForm ell R (s.weight n) u v+
    ((s.scale n)⁻¹ : ℝ)*inner ℂ
      (spectralWeightedPressure R (s.weight n) (s.pressure n)
        (s.pressure_measurable n) (s.pressure_bound n) (spectralHarmonicFirstValue ell R u))
      (spectralHarmonicFirstValue ell R v)

theorem penaltyComplexForm_re (s : SpectralPenaltyFamily R l) (ell n : ℕ)
    (u v : SpectralHarmonicPair ell R) :
    (s.penaltyComplexForm ell n u v).re=s.penaltyForm ell n u v := by
  simp only [penaltyComplexForm,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,spectralHarmonicPairComplexForm_re,realPart_inner]
  rfl

theorem compactPencil_of_complex_tests (s : SpectralPenaltyFamily R l) (ell n : ℕ)
    (hR : 0 < R) (K : SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R)
    (u : SpectralHarmonicPair ell R)
    (hf : ∀ φ : 𝓢(ℝ,ℂ), star (s.penaltyComplexForm ell n u (spectralFirstTest ell R φ))=
      inner ℂ (spectralFirstTest ell R φ) (K (spectralHarmonicObservation ell R hR u)))
    (hg : ∀ φ : 𝓢(ℝ,ℂ), star (s.penaltyComplexForm ell n u (spectralSecondTest ell R φ))=
      inner ℂ (spectralSecondTest ell R φ) (K (spectralHarmonicObservation ell R hR u))) :
    s.compactPencil ell hR n K (spectralHarmonicObservation ell R hR u)=
      spectralHarmonicObservation ell R hR u := by
  apply s.compactPencil_of_smooth_tests ell n hR K u
  · intro φ
    have h := congrArg Complex.re (hf φ)
    simpa only [Complex.star_def,Complex.conj_re,penaltyComplexForm_re,
      spectralHarmonicPairInner_re,real_inner_comm] using h
  · intro φ
    have h := congrArg Complex.re (hg φ)
    simpa only [Complex.star_def,Complex.conj_re,penaltyComplexForm_re,
      spectralHarmonicPairInner_re,real_inner_comm] using h

end SpectralPenaltyFamily
end DefocusingNLS

end OAI
