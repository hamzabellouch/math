import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleInverseEnergy

namespace OAI

/-! The vanishing scaled Liouville Cauchy data control the frequency-weighted
physical boundary energy, with constants depending only on the fixed radius. -/

open Filter Topology
namespace DefocusingNLS

noncomputable def spectralWeightedCauchyEnergy (omega : ℝ) (f g : ℝ → ℂ) (r : ℝ) : ℝ :=
  omega*(‖f r‖^2+‖g r‖^2)+‖deriv f r‖^2+‖deriv g r‖^2

theorem spectralWeightedCauchyEnergy_nonneg (omega : ℝ) (ho : 0 ≤ omega)
    (f g : ℝ → ℂ) (r : ℝ) : 0 ≤ spectralWeightedCauchyEnergy omega f g r := by
  unfold spectralWeightedCauchyEnergy
  positivity

theorem spectralLiouvilleState_inverse_weighted_energy (h r omega : ℝ)
    (hh : |h| ≤ 1) (hr : 0 < r) (ho : 1 ≤ omega) (u v : ℂ) :
    r^11*(omega*‖u‖^2+‖v‖^2) ≤ (3+2*(11/(2*r)+r/4)^2)*
      (omega*‖homogeneousSpectralLocalizationFactor h r*u‖^2+
        ‖homogeneousSpectralLocalizationFactor h r*(v+homogeneousSpectralLocalizationSlope h r*u)‖^2) := by
  have hb := spectralLiouvilleState_inverse_energy h r hh hr u v
  have hv : ‖homogeneousSpectralLocalizationFactor h r*u‖^2 = r^11*‖u‖^2 := by
    rw [norm_mul,mul_pow,spectralLiouvilleFactor_norm_sq h r hr]
  let K := 3+2*(11/(2*r)+r/4)^2
  have hK : 1 ≤ K := by dsimp only [K]; nlinarith [sq_nonneg (11/(2*r)+r/4)]
  have ht : 0 ≤ (K-1)*((omega-1)*‖homogeneousSpectralLocalizationFactor h r*u‖^2) :=
    mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg (sub_nonneg.mpr ho) (sq_nonneg _))
  change _ ≤ K*_
  change _ ≤ K*_ at hb
  calc
    r^11*(omega*‖u‖^2+‖v‖^2) = r^11*(‖u‖^2+‖v‖^2)+
        (omega-1)*‖homogeneousSpectralLocalizationFactor h r*u‖^2 := by rw [hv]; ring
    _ ≤ K*(‖homogeneousSpectralLocalizationFactor h r*u‖^2+
        ‖homogeneousSpectralLocalizationFactor h r*(v+homogeneousSpectralLocalizationSlope h r*u)‖^2)+
        (omega-1)*‖homogeneousSpectralLocalizationFactor h r*u‖^2 := add_le_add hb le_rfl
    _ ≤ _ := by nlinarith only [ht]

theorem spectralPhysicalLiouvillePair_inverse_weighted_energy (r omega : ℝ)
    (hr : 0 < r) (ho : 1 ≤ omega) (f g : ℝ → ℂ) :
    r^11*spectralWeightedCauchyEnergy omega f g r ≤ (3+2*(11/(2*r)+r/4)^2)*
      (omega*‖(spectralPhysicalLiouvillePair f g r).1.1‖^2+
        ‖(spectralPhysicalLiouvillePair f g r).1.2‖^2+
        omega*‖(spectralPhysicalLiouvillePair f g r).2.1‖^2+
        ‖(spectralPhysicalLiouvillePair f g r).2.2‖^2) := by
  have hp := spectralLiouvilleState_inverse_weighted_energy 1 r omega (by norm_num) hr ho (f r) (deriv f r)
  have hm := spectralLiouvilleState_inverse_weighted_energy (-1) r omega (by norm_num) hr ho (g r) (deriv g r)
  dsimp only [spectralWeightedCauchyEnergy,spectralPhysicalLiouvillePair,homogeneousSpectralLocalizationState]
  nlinarith only [hp,hm]

theorem spectralPhysicalLiouvillePair_weighted_energy_limit (R : ℝ) (hR : 0 < R)
    (omega : ℕ → ℝ) (hw : Tendsto omega atTop atTop) (f g : ℕ → ℝ → ℂ)
    (hp : Tendsto (fun n => (Real.sqrt (omega n) : ℂ)*
      (spectralPhysicalLiouvillePair (f n) (g n) R).1.1) atTop (𝓝 0))
    (hm : Tendsto (fun n => (Real.sqrt (omega n) : ℂ)*
      (spectralPhysicalLiouvillePair (f n) (g n) R).2.1) atTop (𝓝 0))
    (hdp : Tendsto (fun n => (spectralPhysicalLiouvillePair (f n) (g n) R).1.2) atTop (𝓝 0))
    (hdm : Tendsto (fun n => (spectralPhysicalLiouvillePair (f n) (g n) R).2.2) atTop (𝓝 0)) :
    Tendsto (fun n => R^11*spectralWeightedCauchyEnergy (omega n) (f n) (g n) R) atTop (𝓝 0) := by
  have hsq {a : ℕ → ℂ} (ha : Tendsto a atTop (𝓝 0)) :
      Tendsto (fun n => ‖a n‖^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero,zero_pow (by decide : 2 ≠ 0)] using ha.norm.pow 2
  have ht := (((hsq hp).add (hsq hdp)).add (hsq hm)).add (hsq hdm)
  have ht' := ht.const_mul (3+2*(11/(2*R)+R/4)^2)
  simp only [add_zero,mul_zero] at ht'
  apply squeeze_zero' _ _ ht'
  · filter_upwards [hw.eventually (eventually_ge_atTop 1)] with n hn
    exact mul_nonneg (pow_nonneg hR.le 11)
      (spectralWeightedCauchyEnergy_nonneg _ (by linarith) _ _ _)
  · filter_upwards [hw.eventually (eventually_ge_atTop 1)] with n hn
    have hb := spectralPhysicalLiouvillePair_inverse_weighted_energy R (omega n) hR hn (f n) (g n)
    simpa only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (show 0 ≤ omega n by linarith)] using hb

end DefocusingNLS

end OAI
