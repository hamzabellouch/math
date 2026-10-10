import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDilationBoundaryBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformVelocityBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformExteriorPressure

namespace OAI

/-! The actual exterior pressure and velocity bounds make the two dilation
boundary forms vanish with the weighted gauge Cauchy energy. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_dilation_boundary_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (R A : ℝ) (hR : innerBoundaryRadius < R) (hA : 0 ≤ A)
    (omega eta : ℕ → ℝ) (hw : Tendsto omega atTop atTop) (he : ∀ i, 0 ≤ eta i)
    (hang : ∀ᶠ i in atTop, eta i ≤ A*omega i)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (hg : ∀ i, ContDiff ℝ 1 (g i))
    (henergy : Tendsto (fun i => radialMassDensity (s i) (z i) R*
      spectralWeightedCauchyEnergy (omega i) (f i) (g i) R) atTop (𝓝 0)) :
    Tendsto (fun i => radialComplexAngularBoundary (s i) (z i) (eta i) R
      ((6-2*radialShootingA (s i))/2) (radialSpectralPressure (s i) (z i)) (f i)) atTop (𝓝 0) ∧
    Tendsto (fun i => radialComplexAngularBoundary (s i) (z i) (eta i) R
      ((6-2*radialShootingA (s i))/2) (fun _ => 0) (g i)) atTop (𝓝 0) := by
  have hR0 : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  obtain ⟨W,hW,hvel⟩ := radialMatched_uniform_velocity_bound s hs z z₀ hz hX hm R hR0.le
  let K := W*(1/R^2+1)+3+W*(A/R^2)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have ht := henergy.const_mul K
  simp only [mul_zero] at ht
  have hb : ∀ᶠ i in atTop,
      |radialComplexAngularBoundary (s i) (z i) (eta i) R
        ((6-2*radialShootingA (s i))/2) (radialSpectralPressure (s i) (z i)) (f i)| ≤
        K*(radialMassDensity (s i) (z i) R*spectralWeightedCauchyEnergy (omega i) (f i) (g i) R) ∧
      |radialComplexAngularBoundary (s i) (z i) (eta i) R
        ((6-2*radialShootingA (s i))/2) (fun _ => 0) (g i)| ≤
        K*(radialMassDensity (s i) (z i) R*spectralWeightedCauchyEnergy (omega i) (f i) (g i) R) := by
    filter_upwards [hvel,hang,hw.eventually (eventually_ge_atTop 1),
      hs.tendsto_atTop.eventually (radialMatched_exterior_pressure_small 1 (by norm_num))] with i hvi hai hoi hqi
    have has := radialShootingA_bounds (s i) (profileMatchingParameter (z i))
    have hshift : |(6-2*radialShootingA (s i))/2| ≤ 3 := by
      apply abs_le.mpr
      constructor <;> linarith
    have hq : |radialSpectralPressure (s i) (z i) R| ≤ 1/R^2 := by
      have hq0 : 0 ≤ radialSpectralPressure (s i) (z i) R := by
        dsimp only [radialSpectralPressure]
        exact div_nonneg (by positivity) has.1.le
      rw [abs_of_nonneg hq0]
      apply (le_div_iff₀ (sq_pos_of_pos hR0)).mpr
      have hh := hqi (z i) R hR
      change R^2*radialSpectralPressure (s i) (z i) R < 1 at hh
      linarith only [hh]
    have hM : 0 ≤ radialMassDensity (s i) (z i) R := by dsimp only [radialMassDensity]; positivity
    have hEf : omega i*‖f i R‖^2+‖deriv (f i) R‖^2 ≤ spectralWeightedCauchyEnergy (omega i) (f i) (g i) R := by
      dsimp only [spectralWeightedCauchyEnergy]
      nlinarith [mul_nonneg (show 0 ≤ omega i by linarith) (sq_nonneg ‖g i R‖),sq_nonneg ‖deriv (g i) R‖]
    have hEg : omega i*‖g i R‖^2+‖deriv (g i) R‖^2 ≤ spectralWeightedCauchyEnergy (omega i) (f i) (g i) R := by
      dsimp only [spectralWeightedCauchyEnergy]
      nlinarith [mul_nonneg (show 0 ≤ omega i by linarith) (sq_nonneg ‖f i R‖),sq_nonneg ‖deriv (f i) R‖]
    have hcoeff := mul_nonneg hK hM
    have hfB := radialComplexAngularBoundary_bound (s i) (z i) R (omega i) (eta i) W (1/R^2) 3 A
      ((6-2*radialShootingA (s i))/2) (radialSpectralPressure (s i) (z i)) (f i)
      hR0 hoi (he i) hW (by positivity) (by norm_num) hA hai (hvi R ⟨hR0.le,le_rfl⟩).1 hshift hq
      ((hf i).differentiable (by norm_num))
    have hgB := radialComplexAngularBoundary_bound (s i) (z i) R (omega i) (eta i) W (1/R^2) 3 A
      ((6-2*radialShootingA (s i))/2) (fun _ => 0) (g i)
      hR0 hoi (he i) hW (by positivity) (by norm_num) hA hai (hvi R ⟨hR0.le,le_rfl⟩).1 hshift (by simp; positivity)
      ((hg i).differentiable (by norm_num))
    constructor
    · exact hfB.trans (by simpa only [K,mul_assoc] using mul_le_mul_of_nonneg_left hEf hcoeff)
    · exact hgB.trans (by simpa only [K,mul_assoc] using mul_le_mul_of_nonneg_left hEg hcoeff)
  constructor
  · exact squeeze_zero_norm' (hb.mono (fun i hi => by simpa only [Real.norm_eq_abs] using hi.1)) ht
  · exact squeeze_zero_norm' (hb.mono (fun i hi => by simpa only [Real.norm_eq_abs] using hi.2)) ht

end DefocusingNLS

end OAI
