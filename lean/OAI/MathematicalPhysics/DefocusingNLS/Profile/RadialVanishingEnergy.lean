import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedMassLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexEnergySplit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergyUpper

namespace OAI

/-! Vanishing gradient energy and weighted boundary data imply vanishing full
gauge energy, and the inverse gauge comparison gives vanishing physical energy. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

variable (s : ℕ → ℕ) (hs : StrictMono s)
  (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z₀))
  (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
    (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
  (hm : ∀ i, radialMatchingMap (s i) (z i)=0)

include s hs z hz hX hm

theorem radialMatched_gradient_to_energy_limit (R : ℝ) (hR : 0 < R)
    (omega eta : ℕ → ℝ) (hw : Tendsto omega atTop atTop) (he : ∀ i, 0 ≤ eta i)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hgradient : Tendsto (fun i => radialComplexAngularForm (s i) (z i) (eta i) R (fun _ => 0) (f i)+
      radialComplexAngularForm (s i) (z i) (eta i) R (fun _ => 0) (g i)) atTop (𝓝 0))
    (hfirst : Tendsto (fun i => ∫ r in (0 : ℝ)..R,
      radialMassDensity (s i) (z i) r*‖f i r‖^2) atTop (𝓝 0))
    (hboundary : Tendsto (fun i => radialMassDensity (s i) (z i) R*
      spectralWeightedCauchyEnergy (omega i) (f i) (g i) R) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ r in (0 : ℝ)..R, radialMatchedMassFunction (s i) (z i) r*
      spectralRadialEnergyDensity (eta i) (f i) (g i) r) atTop (𝓝 0) := by
  have hder : Tendsto (fun i => ∫ r in (0 : ℝ)..R,
      radialMassDensity (s i) (z i) r*‖deriv (g i) r‖^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun i => ?_)) (Eventually.of_forall (fun i => ?_)) hgradient
    · apply intervalIntegral.integral_nonneg hR.le
      intro r hr
      have hr0 := hr.1
      dsimp only [radialMassDensity]
      positivity
    · have hAf : 0 ≤ radialComplexAngularForm (s i) (z i) (eta i) R (fun _ => 0) (f i) :=
        radialComplexAngularForm_zero_nonneg _ _ _ _ (he i) hR.le _
      have hA : 0 ≤ ∫ r in (0 : ℝ)..R, radialAngularDensity (s i) (z i) r*‖g i r‖^2 := by
        apply intervalIntegral.integral_nonneg hR.le
        intro r hr
        have hr0 := hr.1
        dsimp only [radialAngularDensity]
        positivity
      have hG := radialComplexAngularForm_zero_eq (s i) (z i) (hX i) (hm i) (eta i) R (g i) (hg i)
      nlinarith only [hAf,hG,mul_nonneg (he i) hA]
  have htrace := radialMatched_boundary_second_value_limit s hs z z₀ hz hX hm R hR omega hw f g hboundary
  obtain ⟨c,M,hc,hM,_,hb⟩ := radialMatched_uniform_weight_bounds s hs z z₀ hz hX hm R
  have hb' : ∀ᶠ i in atTop, ∀ r ∈ Icc 0 R,
      c ≤ radialMatchedMassFunction (s i) (z i) r ∧ radialMatchedMassFunction (s i) (z i) r ≤ M := by
    filter_upwards [hb] with i hi r hr
    exact ⟨(hi r hr).1,(le_abs_self _).trans (by simpa only [Real.norm_eq_abs,radialMatchedMassFunction] using (hi r hr).2)⟩
  have hsecond := spectralWeightedPoincare_limit R c M hR.le hc hM
    (fun i => radialMatchedMassFunction (s i) (z i))
    (fun i => radialMatchedMassFunction_continuous (s i) (z i) (hX i) (hm i)) hb' g hg hder htrace
  have ht := (hgradient.add hfirst).add hsecond
  simp only [add_zero] at ht
  apply ht.congr
  intro i
  exact (radialComplexEnergy_split (s i) (z i) (hX i) (hm i) (eta i) R (f i) (g i) (hf i) (hg i)).symm

theorem radialMatched_vanishing_physical_energy (R : ℝ) (hR : 0 < R) (eta : ℕ → ℝ)
    (he : ∀ i, 0 ≤ eta i) (F G f g : ℕ → ℝ → ℂ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (hG : ∀ i, ContDiff ℝ 2 (G i))
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (hpair : ∀ i r, (radialMatchedEvenProfile (s i) (z i) r*(f i r+Complex.I*g i r),
      star (radialMatchedEvenProfile (s i) (z i) r)*(f i r-Complex.I*g i r))=(F i r,G i r))
    (henergy : Tendsto (fun i => ∫ r in (0 : ℝ)..R, radialMatchedMassFunction (s i) (z i) r*
      spectralRadialEnergyDensity (eta i) (f i) (g i) r) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ r in (0 : ℝ)..R, spectralRadialEnergyDensity (eta i) (F i) (G i) r) atTop (𝓝 0) := by
  obtain ⟨c,_,hc,_,_,hb⟩ := radialMatched_uniform_weight_bounds s hs z z₀ hz hX hm R
  obtain ⟨D,_,hd⟩ := radialMatched_uniform_derivative_bound s hs z z₀ hz hX hm R hR
  have ht := henergy.const_mul (4+4*D^2/c)
  simp only [mul_zero] at ht
  have hnonneg i : 0 ≤ ∫ r in (0 : ℝ)..R, spectralRadialEnergyDensity (eta i) (F i) (G i) r := by
    apply intervalIntegral.integral_nonneg hR.le
    intro r hr
    have hr0 := hr.1
    have hei := he i
    dsimp only [spectralRadialEnergyDensity,spectralCoordinateEnergy]
    positivity
  apply squeeze_zero' (Eventually.of_forall hnonneg) _ ht
  filter_upwards [hb,hd] with i hi hdi
  have hQi : ContDiff ℝ 2 (radialMatchedEvenProfile (s i) (z i)) :=
    (radialMatchedEvenProfile_contDiff (s i) (z i) (hX i) (hm i)).of_le (by simp)
  have hbound := spectralRadialGaugeEnergy_upper_integral (eta i) c D R hc (he i) hR.le
    (radialMatchedEvenProfile (s i) (z i)) (f i) (g i) (F i) (G i) hQi (hf i) (hg i) (hF i) (hG i)
    (hpair i) (fun r hr => ?_) hdi
  · have heq : (∫ r in (0 : ℝ)..R, ‖radialMatchedEvenProfile (s i) (z i) r‖^2*
        spectralRadialEnergyDensity (eta i) (f i) (g i) r) =
        (∫ r in (0 : ℝ)..R, radialMatchedMassFunction (s i) (z i) r*
        spectralRadialEnergyDensity (eta i) (f i) (g i) r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hR.le] at hr
      dsimp only
      rw [radialMatchedEvenProfile_nonneg (s i) (z i) r hr.1]
      rfl
    simpa only [heq] using hbound
  · simpa only [radialMatchedEvenProfile_nonneg (s i) (z i) r hr.1] using (hi r hr).1

end DefocusingNLS

end OAI
