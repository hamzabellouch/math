import OAI.Geometry.RCD.Heat.SpaceTimeIncrement
import OAI.Geometry.RCD.Harmonic.QuadraticRateOptimization

namespace OAI

/-! # Optimizing a two-time quadratic bound at a differentiability point -/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem spaceTime_localSlope_bound {U : ℝ → X → ℝ} {H : ℝ → ℝ} {x : X}
    {K N t d c : ℝ} (hN : 0 < N) (ht : 0 < t) (hc : 0 < c)
    (hU : HasDerivAt (fun s => U s x) d t) (hH : ContinuousAt H t)
    (hTime : (2*t/N)*d^2 ≤ Real.exp (-2*K*t)*H t)
    (hb : ∀ s, 0 < s → ∀ σ, 0 < σ → σ < c → ∀ y,
      |U s x-U t y| ≤ σ/2*H s+
        Real.exp (-K*(s+t))*(dist x y^2+2*N*(Real.sqrt s-Real.sqrt t)^2)/(2*σ)) :
    (localSlope (U t) x).toReal^2+(2*t/N)*d^2 ≤ Real.exp (-2*K*t)*H t := by
  let A := Real.exp (-2*K*t)
  let C := H t-2*t*d^2/(N*A)
  have hA : 0 < A := Real.exp_pos _
  have hId : A*C=A*H t-(2*t/N)*d^2 := by
    dsimp only [C]
    field_simp
  have hC : 0 ≤ C := by
    apply nonneg_of_mul_nonneg_left (a := C)
    · rw [mul_comm,hId]
      exact sub_nonneg.mpr hTime
    · exact hA
  have hslope (ell : ℝ) (hell : 0 < ell) :
      (localSlope (U t) x).toReal ≤ ell/2*C+A/(2*ell) := by
    let α := 2*t*ell*d/(N*A)
    let Rp := spaceTimeSlopeRate (fun s => U s x) H K N t α ell
    let Rm := spaceTimeSlopeRate (fun s => -U s x) H K N t (-α) ell
    have heq : ell/2*H t+Real.exp (-2*K*t)*(1+N*α^2/(2*t))/(2*ell)-α*d =
        ell/2*C+A/(2*ell) := optimized_spaceTimeSlopeRate hA hN hell
    have hp := spaceTimeSlopeRate_tendsto ht hU hH K N α ell
    rw [heq] at hp
    have hm := spaceTimeSlopeRate_tendsto ht hU.neg hH K N (-α) ell
    rw [show (-(fun s => U s x)) = (fun s => -U s x) from rfl] at hm
    have heqm : ell/2*H t+Real.exp (-2*K*t)*(1+N*(-α)^2/(2*t))/(2*ell)-(-α)*(-d) =
        ell/2*C+A/(2*ell) := by simpa only [neg_sq,neg_mul_neg] using heq
    rw [heqm] at hm
    have hlim : Tendsto (fun r => max (Rp r) (Rm r)) (𝓝[>] 0)
        (𝓝 (ell/2*C+A/(2*ell))) := by simpa only [max_self,Pi.neg_apply,Rp,Rm] using hp.max hm
    apply localSlope_le_of_rate_limit (by positivity) hlim
    have htp : ∀ᶠ r in 𝓝 (0:ℝ), 0 < t+α*r :=
      ((show Continuous (fun r : ℝ => t+α*r) by fun_prop).continuousAt (x := 0)).eventually
        (Ioi_mem_nhds (by simpa only [mul_zero,add_zero] using ht))
    have htm : ∀ᶠ r in 𝓝 (0:ℝ), 0 < t+(-α)*r :=
      ((show Continuous (fun r : ℝ => t+(-α)*r) by fun_prop).continuousAt (x := 0)).eventually
        (Ioi_mem_nhds (by simpa only [mul_zero,add_zero] using ht))
    have hsc : ∀ᶠ r in 𝓝 (0:ℝ), ell*r < c :=
      ((show Continuous (fun r : ℝ => ell*r) by fun_prop).continuousAt (x := 0)).eventually
        (Iio_mem_nhds (by simpa only [mul_zero] using hc))
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds htp,
      nhdsWithin_le_nhds htm,nhdsWithin_le_nhds hsc] with r hr htp htm hsc
    intro y hxy
    have hp' := spaceTimeSlopeRate_increment hell hr hxy
      ((le_abs_self _).trans (hb _ htp _ (mul_pos hell hr) hsc y))
    have hbm : (-U (t+(-α)*r) x)-(-U t y) ≤ ell*r/2*H (t+(-α)*r)+
        Real.exp (-K*((t+(-α)*r)+t))*(dist x y^2+2*N*(Real.sqrt (t+(-α)*r)-Real.sqrt t)^2)/(2*(ell*r)) := by
      have hh := (neg_le_abs (U (t+(-α)*r) x-U t y)).trans
        (hb _ htm _ (mul_pos hell hr) hsc y)
      linarith only [hh]
    have hm' := spaceTimeSlopeRate_increment (U := fun s y => -U s y) hell hr hxy hbm
    have hpmax : U t x-U t y ≤ max (Rp r) (Rm r)*r :=
      hp'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le)
    have hmmax : -U t x-(-U t y) ≤ max (Rp r) (Rm r)*r :=
      hm'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le)
    exact abs_le.mpr ⟨by linarith only [hmmax],hpmax⟩
  have hs := square_le_of_young_bounds (g := (localSlope (U t) x).toReal) ENNReal.toReal_nonneg hC hA (by
    intro ell hell
    calc _ ≤ ell/2*C+A/(2*ell) := hslope ell hell
      _ = _ := by ring)
  rw [hId] at hs
  change _ ≤ A*H t
  linarith only [hs]

end RegularPointCoordinates

end

end OAI
