import OAI.Geometry.RCD.Heat.SpaceTimeSlopeRate

namespace OAI

/-! # The temporal part of the dimensional quadratic bound -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

def timeQuadraticRate (U H : ℝ → ℝ) (K N t α r : ℝ) : ℝ :=
  spaceTimeSlopeRate U H K N t α 1 r-Real.exp (-K*((t+α*r)+t))/2

theorem timeQuadraticRate_tendsto {U H : ℝ → ℝ} {t d : ℝ}
    (ht : 0 < t) (hU : HasDerivAt U d t) (hH : ContinuousAt H t) (K N α : ℝ) :
    Tendsto (timeQuadraticRate U H K N t α) (𝓝[>] 0)
      (𝓝 (H t/2+Real.exp (-2*K*t)*N*α^2/(4*t)-α*d)) := by
  have he : Tendsto (fun r : ℝ => Real.exp (-K*((t+α*r)+t))/2) (𝓝[>] 0)
      (𝓝 (Real.exp (-2*K*t)/2)) := by
    rw [show -2*K*t = -K*(t+t) by ring]
    simpa only [mul_zero,add_zero] using
      ((show Continuous (fun r : ℝ => Real.exp (-K*((t+α*r)+t))/2)
        by fun_prop).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hh := (spaceTimeSlopeRate_tendsto ht hU hH K N α 1).sub he
  have heq : 1/2*H t+Real.exp (-2*K*t)*(1+N*α^2/(2*t))/(2*1)-α*d-
      Real.exp (-2*K*t)/2 = H t/2+Real.exp (-2*K*t)*N*α^2/(4*t)-α*d := by ring
  rw [←heq]
  exact hh

theorem timeQuadraticRate_nonneg {U H : ℝ → ℝ} {K N t α r : ℝ} (hr : 0 < r)
    (hb : U (t+α*r)-U t ≤ r/2*H (t+α*r)+
      Real.exp (-K*((t+α*r)+t))*(2*N*(Real.sqrt (t+α*r)-Real.sqrt t)^2)/(2*r)) :
    0 ≤ timeQuadraticRate U H K N t α r := by
  have hh := div_nonneg (sub_nonneg.mpr hb) hr.le
  convert hh using 1
  dsimp only [timeQuadraticRate,spaceTimeSlopeRate]
  field_simp
  ring

end RegularPointCoordinates

end

end OAI
