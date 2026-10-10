import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformVelocityBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleWeightedEnergy

namespace OAI

/-! Vanishing weighted boundary energy controls both the ordinary cross
boundary term and the cross term multiplied by the spectral frequency. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem spectralCrossBoundary_bound (M V W omega : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (ho : 1 ≤ omega) (hV : |V| ≤ W*M) (f g df dg : ℂ) :
    ‖(V : ℂ)*star f*g‖ ≤ W*M*(omega*(‖f‖^2+‖g‖^2)+‖df‖^2+‖dg‖^2) ∧
    ‖(omega : ℂ)*((V : ℂ)*star f*g)‖ ≤
      W*M*(omega*(‖f‖^2+‖g‖^2)+‖df‖^2+‖dg‖^2) := by
  have ho0 : 0 ≤ omega := by linarith
  have hp : ‖f‖*‖g‖ ≤ ‖f‖^2+‖g‖^2 := by nlinarith [sq_nonneg (‖f‖-‖g‖)]
  have ht := mul_le_mul_of_nonneg_left hp ho0
  have he := mul_le_mul_of_nonneg_right ho (add_nonneg (sq_nonneg ‖f‖) (sq_nonneg ‖g‖))
  have hd : 0 ≤ ‖df‖^2+‖dg‖^2 := by positivity
  have hb : ‖(V : ℂ)*star f*g‖ ≤ W*M*(‖f‖*‖g‖) := by
    simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hV (mul_nonneg (norm_nonneg f) (norm_nonneg g))
  constructor
  · exact hb.trans (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hW hM))
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho0]
    calc
      _ ≤ omega*(W*M*(‖f‖*‖g‖)) := mul_le_mul_of_nonneg_left hb ho0
      _ = W*M*(omega*(‖f‖*‖g‖)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hW hM)

theorem radialMatched_dilation_cross_boundary_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (R : ℝ) (hR : 0 ≤ R) (omega : ℕ → ℝ) (hw : Tendsto omega atTop atTop)
    (f g : ℕ → ℝ → ℂ)
    (henergy : Tendsto (fun i => radialMassDensity (s i) (z i) R*
      spectralWeightedCauchyEnergy (omega i) (f i) (g i) R) atTop (𝓝 0)) :
    Tendsto (fun i => (radialMassFlux (s i) (z i) R : ℂ)*star (f i R)*g i R) atTop (𝓝 0) ∧
    Tendsto (fun i => (omega i : ℂ)*((radialMassFlux (s i) (z i) R : ℂ)*star (f i R)*g i R)) atTop (𝓝 0) := by
  obtain ⟨W,hW,hvel⟩ := radialMatched_uniform_velocity_bound s hs z z₀ hz hX hm R hR
  have ht := henergy.const_mul W
  simp only [mul_zero] at ht
  have hb : ∀ᶠ i in atTop,
      ‖(radialMassFlux (s i) (z i) R : ℂ)*star (f i R)*g i R‖ ≤ W*(radialMassDensity (s i) (z i) R*
        spectralWeightedCauchyEnergy (omega i) (f i) (g i) R) ∧
      ‖(omega i : ℂ)*((radialMassFlux (s i) (z i) R : ℂ)*star (f i R)*g i R)‖ ≤
        W*(radialMassDensity (s i) (z i) R*spectralWeightedCauchyEnergy (omega i) (f i) (g i) R) := by
    filter_upwards [hvel,hw.eventually (eventually_ge_atTop 1)] with i hi hoi
    have hh := spectralCrossBoundary_bound (radialMassDensity (s i) (z i) R)
      (radialMassFlux (s i) (z i) R) W (omega i) (by dsimp only [radialMassDensity]; positivity)
      hW hoi (hi R ⟨hR,le_rfl⟩).2 (f i R) (g i R) (deriv (f i) R) (deriv (g i) R)
    simpa only [spectralWeightedCauchyEnergy,mul_assoc] using hh
  exact ⟨squeeze_zero_norm' (hb.mono (fun _ h => h.1)) ht,
    squeeze_zero_norm' (hb.mono (fun _ h => h.2)) ht⟩

end DefocusingNLS

end OAI
