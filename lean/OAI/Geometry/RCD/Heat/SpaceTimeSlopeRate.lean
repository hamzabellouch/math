import OAI.Geometry.RCD.Heat.TwoTimeCostLimit
import OAI.Geometry.RCD.Sobolev.LocalSlopeRateLimit

namespace OAI

/-! # Scalar rates for the space-time quadratic inequality -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

def spaceTimeSlopeRate (U H : ℝ → ℝ) (K N t α ell r : ℝ) : ℝ :=
  ell/2*H (t+α*r)+Real.exp (-K*((t+α*r)+t))*
    (1+2*N*((Real.sqrt (t+α*r)-Real.sqrt t)/r)^2)/(2*ell)-
    (U (t+α*r)-U t)/r

theorem spaceTimeSlopeRate_tendsto {U H : ℝ → ℝ} {t d : ℝ}
    (ht : 0 < t) (hU : HasDerivAt U d t) (hH : ContinuousAt H t) (K N α ell : ℝ) :
    Tendsto (spaceTimeSlopeRate U H K N t α ell) (𝓝[>] 0)
      (𝓝 (ell/2*H t+Real.exp (-2*K*t)*(1+N*α^2/(2*t))/(2*ell)-α*d)) := by
  have hl : Tendsto (fun r : ℝ => t+α*r) (𝓝[>] 0) (𝓝 t) := by
    simpa only [mul_zero,add_zero] using
      ((show Continuous (fun r : ℝ => t+α*r) by fun_prop).continuousAt (x := 0)).tendsto.mono_left
        nhdsWithin_le_nhds
  exact ((hH.tendsto.comp hl).const_mul (ell/2)).add
    ((two_time_cost_ratio_tendsto ht K N α).div_const (2*ell)) |>.sub
      (affine_time_difference_tendsto hU α)

theorem optimized_spaceTimeSlopeRate {A N t d H ell : ℝ}
    (hA : 0 < A) (hN : 0 < N) (hell : 0 < ell) :
    let α := 2*t*ell*d/(N*A)
    ell/2*H+A*(1+N*α^2/(2*t))/(2*ell)-α*d =
      ell/2*(H-2*t*d^2/(N*A))+A/(2*ell) := by
  dsimp only
  field_simp
  ring

end RegularPointCoordinates

end

end OAI
