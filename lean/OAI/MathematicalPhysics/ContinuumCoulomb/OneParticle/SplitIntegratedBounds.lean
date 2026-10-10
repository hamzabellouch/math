import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitFormIntegrals

namespace OAI

/-! Actual integrated form bounds. The premises name only the published
isolated-well and harmonic-oscillator spectral results. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem splitPlanarForm_projection_lower
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η : ℝ), 8 ≤ D → 0 < η →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      ∀ f : SplitPosition → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      ((-1/2:ℝ)+γ-planarSiteDerivativeBound D^2-
        γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8)))*(∫ p, f p^2) -
        γ*(1+η)*(∫ z, ∑ i, (planarCoefficient (u i) f z)^2) ≤ splitPlanarForm u f := by
  obtain ⟨γ,hγ,hsmall,hbound⟩ := planarWellSum_test_projection_bound hpublished
  refine ⟨γ,hγ,hsmall,fun m D η hD hη u hsep f hf hc => ?_⟩
  have hL2 : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hc
  have hmass : Integrable (fun z : ℝ => ∫ r : PlanarPosition, f (r,z)^2) := by
    have hi : Integrable (fun p : SplitPosition => f p^2) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hL2.integrable_sq
    exact hi.integral_prod_right
  have hcoeff : Integrable (fun z : ℝ => ∑ i, (planarCoefficient (u i) f z)^2) :=
    integrable_finsetSum _ (fun i _ => (planarCoefficient_contraction (u i) f hL2).1.integrable_sq)
  have hb := integral_mono
    ((hmass.const_mul _).sub (hcoeff.const_mul _))
    (split_planar_form_integrable u hf hc)
    (fun z => hbound m D η hD hη u hsep (fun r => f (r,z))
      (split_planar_slice_contDiff hf z) (compact_planar_slice hc z))
  simp only [Pi.sub_apply] at hb
  rw [integral_sub (hmass.const_mul _) (hcoeff.const_mul _),
    integral_const_mul, integral_const_mul, split_planar_mass_integral hL2] at hb
  exact hb

theorem splitVerticalForm_projection_lower
    (hpublished : PublishedVerticalOscillatorGap)
    {freq S η : ℝ} (hfreq : 0 < freq) (hS : 0 < S) (hη : 0 < η)
    (hbarrier : 3*freq/2 ≤ freq^2*S^2/8)
    (f : SplitPosition → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (3*freq/2-verticalCutoffDerivativeBound S^2/2-
      freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8))*(∫ p, f p^2) -
      freq*(1+η)*(∫ r, (verticalCoefficient freq f r)^2) ≤ splitVerticalForm freq S f := by
  have hL2 : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hc
  have hmass : Integrable (fun r : PlanarPosition => ∫ z : ℝ, f (r,z)^2) := by
    have hi : Integrable (fun p : SplitPosition => f p^2) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hL2.integrable_sq
    exact hi.integral_prod_left
  have hcoeff := (verticalCoefficient_contraction hfreq f hL2).1.integrable_sq
  have hb := integral_mono
    ((hmass.const_mul _).sub (hcoeff.const_mul _))
    (split_vertical_form_integrable freq S hf hc)
    (fun r => verticalCappedForm_global_projection_lower hpublished hfreq hS hη hbarrier
      (fun z => f (r,z)) (split_vertical_slice_contDiff hf r) (compact_vertical_slice hc r))
  simp only [Pi.sub_apply] at hb
  rw [integral_sub (hmass.const_mul _) (hcoeff.const_mul _),
    integral_const_mul, integral_const_mul, split_vertical_mass_integral hL2] at hb
  exact hb

/-- Conditional on the two precisely stated published spectral inputs, this
is a finite-rank lower bound for the actual split-coordinate Schrödinger form. -/
theorem split_test_spectral_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S : ℝ),
      8 ≤ D → 0 < η → 0 < freq → 0 < S → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      ∀ f : SplitPosition → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      (((-1/2:ℝ)+γ-planarSiteDerivativeBound D^2-
        γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))) +
        (3*freq/2-verticalCutoffDerivativeBound S^2/2-
          freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)) -
        freq*(1+η))*(∫ p, f p^2) -
        γ*(1+η)*(∑ i, (∫ p, f p*localizedMode freq (u i) p)^2) ≤
        splitPlanarForm u f+splitVerticalForm freq S f := by
  obtain ⟨γ,hγ,hsmall,hplanar⟩ := splitPlanarForm_projection_lower hp
  refine ⟨γ,hγ,hsmall,fun m D η freq S hD hη hfreq hS hbarrier u hsep hdom f hf hc => ?_⟩
  exact split_form_projection_lower hfreq (mul_nonneg hγ.le (by positivity)) u hsep hdom f
    (hf.continuous.memLp_of_hasCompactSupport hc)
    (hplanar m D η hD hη u hsep f hf hc)
    (splitVerticalForm_projection_lower hv hfreq hS hη hbarrier f hf hc)

end ContinuumCoulomb

end

end OAI
