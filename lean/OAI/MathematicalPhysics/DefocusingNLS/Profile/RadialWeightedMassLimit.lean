import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialPoincare
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedGaugeBoundary

namespace OAI

/-! The fixed-ball Poincare estimate converts vanishing radial derivative
energy and the derived boundary trace into vanishing weighted value mass. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralWeightedPoincare_limit (R c M : ℝ) (hR : 0 ≤ R) (hc : 0 < c) (hM : 0 ≤ M)
    (mu : ℕ → ℝ → ℝ) (hmu : ∀ i, Continuous (mu i))
    (hbounds : ∀ᶠ i in atTop, ∀ r ∈ Icc 0 R, c ≤ mu i r ∧ mu i r ≤ M)
    (f : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hder : Tendsto (fun i => ∫ r in (0 : ℝ)..R, r^11*mu i r*‖deriv (f i) r‖^2) atTop (𝓝 0))
    (htrace : Tendsto (fun i => ‖f i R‖^2) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ r in (0 : ℝ)..R, r^11*mu i r*‖f i r‖^2) atTop (𝓝 0) := by
  have ht := ((hder.const_mul (M*R^2)).add (htrace.const_mul (4*c*M*R^12))).div_const (16*c)
  simp only [mul_zero,add_zero,zero_div] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [hbounds] with i hi
    apply intervalIntegral.integral_nonneg hR
    intro r hr
    exact mul_nonneg (mul_nonneg (pow_nonneg hr.1 11) (hc.le.trans (hi r hr).1)) (sq_nonneg _)
  · filter_upwards [hbounds] with i hi
    apply (le_div_iff₀ (by positivity : 0 < 16*c)).mpr
    have h := spectralRadial_weightedPoincare R c M hR hc hM (mu i) (hmu i) hi (f i) (hf i)
    simpa only [mul_comm] using h

theorem radialMatched_boundary_second_value_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (R : ℝ) (hR : 0 < R) (omega : ℕ → ℝ) (hw : Tendsto omega atTop atTop) (f g : ℕ → ℝ → ℂ)
    (hboundary : Tendsto (fun i => radialMassDensity (s i) (z i) R*
      spectralWeightedCauchyEnergy (omega i) (f i) (g i) R) atTop (𝓝 0)) :
    Tendsto (fun i => ‖g i R‖^2) atTop (𝓝 0) := by
  obtain ⟨c,_,hc,_,_,hb⟩ := radialMatched_uniform_weight_bounds s hs z z₀ hz hX hm R
  have ht := hboundary.div_const (c*R^11)
  simp only [zero_div] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) _ ht
  filter_upwards [hb,hw.eventually (eventually_ge_atTop 1)] with i hi hoi
  apply (le_div_iff₀ (by positivity : 0 < c*R^11)).mpr
  have hM : c*R^11 ≤ radialMassDensity (s i) (z i) R := by
    have hh := mul_le_mul_of_nonneg_left (hi R ⟨hR.le,le_rfl⟩).1 (pow_nonneg hR.le 11)
    simpa only [radialMassDensity,mul_comm] using hh
  have hE : ‖g i R‖^2 ≤ spectralWeightedCauchyEnergy (omega i) (f i) (g i) R := by
    dsimp only [spectralWeightedCauchyEnergy]
    nlinarith [mul_nonneg (show 0 ≤ omega i by linarith) (sq_nonneg ‖f i R‖),
      sq_nonneg ‖g i R‖,sq_nonneg ‖deriv (f i) R‖,sq_nonneg ‖deriv (g i) R‖]
  have hh := mul_le_mul hM hE (sq_nonneg _) (by dsimp only [radialMassDensity]; positivity)
  simpa only [mul_comm] using hh

end DefocusingNLS

end OAI
