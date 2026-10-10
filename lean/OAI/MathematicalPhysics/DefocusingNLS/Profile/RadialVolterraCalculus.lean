import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVolterraWeight

namespace OAI

/-! Locality and the radial differential equation of the Volterra integral. -/

open Set
namespace DefocusingNLS

theorem radialAverage_congr (f g : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hfg : EqOn f g (Icc 0 r)) : radialAverage f r=radialAverage g r := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  dsimp only
  rw [hfg ⟨mul_nonneg hr hs.1,mul_le_of_le_one_right hr hs.2⟩]

theorem radialVolterra_congr (f g : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hfg : EqOn f g (Icc 0 r)) : radialVolterra f r=radialVolterra g r := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hr] at ht
  dsimp only
  rw [radialAverage_congr f g t ht.1 (fun s hs => hfg ⟨hs.1,hs.2.trans ht.2⟩)]

theorem radialVolterra_zero (f : ℝ → ℝ) : radialVolterra f 0=0 := by
  simp only [radialVolterra,intervalIntegral.integral_same]

theorem radialVolterra_radial_equation (f : ℝ → ℝ) (hf : Continuous f)
    (r : ℝ) (hr : r ≠ 0) :
    deriv (deriv (radialVolterra f)) r+11/r*deriv (radialVolterra f) r=f r := by
  have he : deriv (radialVolterra f)=fun t => t*radialAverage f t := by
    funext t
    exact (hasDerivAt_radialVolterra f hf t).deriv
  have hd := ((hasDerivAt_id r).mul (hasDerivAt_radialAverage f hf r hr)).deriv
  change deriv (fun t : ℝ => t*radialAverage f t) r = _ at hd
  simp only [id_eq] at hd
  rw [he,hd]
  dsimp only
  field_simp [hr]
  ring

end DefocusingNLS

end OAI
