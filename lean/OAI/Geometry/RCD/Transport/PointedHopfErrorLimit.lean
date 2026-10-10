import OAI.Geometry.RCD.Transport.PointedHopfSlope

namespace OAI

/-! # Vanishing quantitative errors for the metric recovery -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem pointedHopfError_tendsto {t M : ℝ} {ε e : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun k => pointedHopfError t M (ε k) (e k)) atTop (𝓝 0) := by
  have hc : Continuous (fun p : ℝ×ℝ => pointedHopfError t M p.1 p.2) := by
    unfold pointedHopfError
    fun_prop
  simpa only [pointedHopfError,Function.comp_def,mul_zero,zero_mul,add_zero,zero_div] using
    hc.continuousAt.tendsto.comp (hε.prodMk_nhds he)

theorem pointedHopfSlopeError_tendsto {t M : ℝ} {ε e : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun k => (Real.sqrt (2*t*pointedHopfError t M (ε k) (e k))+ε k)/t)
      atTop (𝓝 0) := by
  have h := (((pointedHopfError_tendsto (t:=t) (M:=M) hε he).const_mul (2*t)).sqrt.add hε).div_const t
  simpa only [mul_zero,Real.sqrt_zero,zero_add,zero_div] using h

end RegularPointCoordinates

end

end OAI
