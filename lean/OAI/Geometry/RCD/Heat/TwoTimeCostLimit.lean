import OAI.Geometry.RCD.Heat.HeatPointwiseTwoTimeDual

namespace OAI

/-! # The infinitesimal time coefficient in the two-time transport estimate -/

open Filter
open scoped Topology
namespace RegularPointCoordinates

theorem affine_time_difference_tendsto {f : ℝ → ℝ} {t d : ℝ}
    (hd : HasDerivAt f d t) (α : ℝ) :
    Tendsto (fun h : ℝ => (f (t+α*h)-f t)/h) (𝓝[>] 0) (𝓝 (α*d)) := by
  have hlin : HasDerivAt (fun h : ℝ => t+α*h) α 0 := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id (0:ℝ)).const_mul α).const_add t
  have hd' : HasDerivAt f d (t+α*(0:ℝ)) := by simpa only [mul_zero,add_zero] using hd
  have h := (hd'.comp 0 hlin).tendsto_slope_zero_right
  simpa only [Function.comp_def,mul_zero,add_zero,zero_add,smul_eq_mul,div_eq_mul_inv,mul_comm] using h

theorem two_time_cost_ratio_tendsto {t : ℝ} (ht : 0 < t) (K N α : ℝ) :
    Tendsto (fun h : ℝ => Real.exp (-K*((t+α*h)+t))*
      (1+2*N*((Real.sqrt (t+α*h)-Real.sqrt t)/h)^2)) (𝓝[>] 0)
      (𝓝 (Real.exp (-2*K*t)*(1+N*α^2/(2*t)))) := by
  have hs := affine_time_difference_tendsto (Real.hasDerivAt_sqrt ht.ne') α
  have he : Tendsto (fun h : ℝ => Real.exp (-K*((t+α*h)+t))) (𝓝[>] 0)
      (𝓝 (Real.exp (-K*(t+t)))) := by
    simpa only [mul_zero,add_zero] using
      ((show Continuous (fun h : ℝ => Real.exp (-K*((t+α*h)+t))) by fun_prop).continuousAt
        (x := 0)).continuousWithinAt.tendsto (s := Set.Ioi 0)
  have hh := he.mul ((tendsto_const_nhds (x := (1:ℝ))).add ((hs.pow 2).const_mul (2*N)))
  have heq : -K*(t+t) = -2*K*t := by ring
  have hc : 2*N*(α*(1/(2*Real.sqrt t)))^2 = N*α^2/(2*t) := by
    field_simp
    rw [Real.sq_sqrt ht.le]
  rw [heq,hc] at hh
  exact hh

end RegularPointCoordinates

end OAI
