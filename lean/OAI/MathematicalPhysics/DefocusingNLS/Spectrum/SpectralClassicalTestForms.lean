import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalPairing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralContinuousMultiplier

namespace OAI

/-! Exact scalar test forms for classical representatives of energy vectors. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

noncomputable def spectralClassicalRadialPairing (R : ℝ) (q : ℝ → ℝ)
    (f : ℝ → ℂ) (φ : ℝ → ℂ) : ℂ :=
  ∫ r, star (φ r)*(q r • f r) ∂radialPressureMeasure R

noncomputable def spectralClassicalAngularPairing (R : ℝ) (q : ℝ → ℝ)
    (f : ℝ → ℂ) (φ : ℝ → ℂ) : ℂ :=
  ∫ r, star (φ r)*(q r • f r) ∂spectralAngularMeasure R

theorem spectralClassicalMultiplier_pairing (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicEnergy ell R) (f : ℝ → ℂ)
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u r=f r)
    (φ : ℝ → ℂ) (v : SpectralRadialL2 R)
    (hv : v =ᵐ[radialPressureMeasure R] φ) :
    inner ℂ v (spectralRadialWeightMultiplier R w (spectralHarmonicValue ell R u))=
      spectralClassicalRadialPairing R w.density f φ := by
  unfold spectralRadialWeightMultiplier
  rw [spectralL2ComplexMultiplier_pairing_test _ _ _ _ _ _ _ _ hv]
  apply integral_congr_ae
  filter_upwards [spectralHarmonicValue_classical_ae ell R hR u f hf] with r hr
  rw [hr]

namespace SpectralPenaltyFamily
variable {R l : ℝ}

theorem penaltyComplexForm_first_classical (s : SpectralPenaltyFamily R l)
    (ell n : ℕ) (hR : 0 < R) (u : SpectralHarmonicPair ell R) (f : ℝ → ℂ)
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hd : spectralHarmonicDerivative ell R u.fst =ᵐ[radialPressureMeasure R] deriv f)
    (φ : 𝓢(ℝ,ℂ)) :
    star (s.penaltyComplexForm ell n u (spectralFirstTest ell R φ))=
      spectralClassicalRadialPairing R (s.weight n).density f φ+
      spectralClassicalRadialPairing R (s.weight n).density (deriv f) (deriv φ)+
      (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
        spectralClassicalAngularPairing R (s.weight n).density f φ+
      ((s.scale n)⁻¹ : ℝ)*spectralClassicalRadialPairing R
        (fun r => (s.weight n).density r*s.pressure n r) f φ := by
  have hz : spectralHarmonicComplexForm ell R (s.weight n) u.snd 0=0 := by
    simp only [spectralHarmonicComplexForm,map_zero,inner_zero_right,add_zero]
  change star (spectralHarmonicComplexForm ell R (s.weight n) u.fst
      (spectralHarmonicSmoothEmbedding ell R φ)+
      spectralHarmonicComplexForm ell R (s.weight n) u.snd 0+
      ((s.scale n)⁻¹ : ℝ)*inner ℂ
        (spectralWeightedPressure R (s.weight n) (s.pressure n)
          (s.pressure_measurable n) (s.pressure_bound n) (spectralHarmonicValue ell R u.fst))
        (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R φ)))=_
  have hreal : star (((s.scale n)⁻¹ : ℝ) : ℂ)=((s.scale n)⁻¹ : ℝ) := by simp
  rw [hz,add_zero,star_add,star_mul,hreal,spectral_star_inner,
    spectralHarmonicScalar_classical_pairing ell R hR _ _ _ hf hd,
    spectralPressure_classical_pairing ell R hR _ _ _ _ _ _ hf]
  dsimp only [spectralClassicalRadialPairing,spectralClassicalAngularPairing]
  ring

theorem penaltyComplexForm_second_classical (s : SpectralPenaltyFamily R l)
    (ell n : ℕ) (hR : 0 < R) (u : SpectralHarmonicPair ell R) (g : ℝ → ℂ)
    (hg : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (hd : spectralHarmonicDerivative ell R u.snd =ᵐ[radialPressureMeasure R] deriv g)
    (φ : 𝓢(ℝ,ℂ)) :
    star (s.penaltyComplexForm ell n u (spectralSecondTest ell R φ))=
      spectralClassicalRadialPairing R (s.weight n).density g φ+
      spectralClassicalRadialPairing R (s.weight n).density (deriv g) (deriv φ)+
      (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*
        spectralClassicalAngularPairing R (s.weight n).density g φ := by
  have hz : spectralHarmonicComplexForm ell R (s.weight n) u.fst 0=0 := by
    simp only [spectralHarmonicComplexForm,map_zero,inner_zero_right,add_zero]
  change star (spectralHarmonicComplexForm ell R (s.weight n) u.fst 0+
      spectralHarmonicComplexForm ell R (s.weight n) u.snd
        (spectralHarmonicSmoothEmbedding ell R φ)+
      ((s.scale n)⁻¹ : ℝ)*inner ℂ
        (spectralWeightedPressure R (s.weight n) (s.pressure n)
          (s.pressure_measurable n) (s.pressure_bound n) (spectralHarmonicValue ell R u.fst))
        (spectralHarmonicValue ell R 0))=_
  rw [hz,zero_add,map_zero,inner_zero_right,mul_zero,add_zero]
  exact spectralHarmonicScalar_classical_pairing ell R hR _ _ _ hg hd φ

end SpectralPenaltyFamily

theorem spectralLowerOrder_first_classical (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (c ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (u : SpectralHarmonicPair ell R) (f g : ℝ → ℂ)
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hg : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (φ : 𝓢(ℝ,ℂ)) :
    inner ℂ (spectralFirstTest ell R φ)
      (spectralLowerOrderOperator ell R hR (spectralRadialWeightMultiplier R w)
        (spectralRadialWeightMultiplier R a) c ζ B (spectralHarmonicObservation ell R hR u))=
      spectralClassicalRadialPairing R w.density f φ+
      (c-ζ)*spectralClassicalRadialPairing R w.density g φ+
      spectralClassicalRadialPairing R a.density g (deriv φ)+
      star (φ R)*(B (f R,g R)).1 := by
  rw [spectralLowerOrderOperator_inner]
  unfold spectralWeakPairing
  rw [spectralFirstTest_values,spectralFirstTest_derivatives,spectralFirstTest_traces,
    spectralHarmonicObservation_coordinates]
  simp only [inner_zero_left,sub_zero,add_zero,RCLike.inner_apply',starRingEnd_apply,
    star_zero,zero_mul]
  rw [spectralClassicalMultiplier_pairing ell R hR w u.fst f hf _ _
    (spectralHarmonicValue_smooth_ae ell R φ),
    spectralClassicalMultiplier_pairing ell R hR w u.snd g hg _ _
      (spectralHarmonicValue_smooth_ae ell R φ),
    spectralClassicalMultiplier_pairing ell R hR a u.snd g hg _ _
      (spectralHarmonicDerivative_smooth_ae ell R φ),
    hf R ⟨hR,le_rfl⟩,hg R ⟨hR,le_rfl⟩]

theorem spectralLowerOrder_second_classical (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w a : SpectralHarmonicWeight R) (c ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (u : SpectralHarmonicPair ell R) (f g : ℝ → ℂ)
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hg : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (φ : 𝓢(ℝ,ℂ)) :
    inner ℂ (spectralSecondTest ell R φ)
      (spectralLowerOrderOperator ell R hR (spectralRadialWeightMultiplier R w)
        (spectralRadialWeightMultiplier R a) c ζ B (spectralHarmonicObservation ell R hR u))=
      spectralClassicalRadialPairing R w.density g φ-
      (c-ζ)*spectralClassicalRadialPairing R w.density f φ-
      spectralClassicalRadialPairing R a.density f (deriv φ)+
      star (φ R)*(B (f R,g R)).2 := by
  rw [spectralLowerOrderOperator_inner]
  unfold spectralWeakPairing
  rw [spectralSecondTest_values,spectralSecondTest_derivatives,spectralSecondTest_traces,
    spectralHarmonicObservation_coordinates]
  simp only [inner_zero_left,zero_sub,zero_add,RCLike.inner_apply',starRingEnd_apply,
    star_zero,zero_mul]
  rw [spectralClassicalMultiplier_pairing ell R hR w u.snd g hg _ _
    (spectralHarmonicValue_smooth_ae ell R φ),
    spectralClassicalMultiplier_pairing ell R hR w u.fst f hf _ _
      (spectralHarmonicValue_smooth_ae ell R φ),
    spectralClassicalMultiplier_pairing ell R hR a u.fst f hf _ _
      (spectralHarmonicDerivative_smooth_ae ell R φ),
    hf R ⟨hR,le_rfl⟩,hg R ⟨hR,le_rfl⟩]
  ring

end DefocusingNLS

end OAI
