import OAI.Geometry.RCD.Heat.RiccatiFiniteInterval

namespace OAI

/-! # The initial bound from a finite positive-time Riccati inequality

The derivative is needed only at positive times. Continuity handles the
initial value, and no value or regularity is assumed at the final endpoint.
-/

open Set Filter
open scoped Topology
namespace RegularPointCoordinates

theorem riccati_initial_bound {Y : ℝ → ℝ} {T A r : ℝ}
    (hT : 0<T) (hA : 0<A) (h0 : ContinuousAt Y 0)
    (hc : ContinuousOn Y (Ico 0 T))
    (hd : ∀ x∈Ioo 0 T, ∃ rate : ℝ, HasDerivAt Y rate x ∧
      (r≤Y x → A*(Y x-r)^2≤rate)) :
    Y 0≤r+1/(A*T) := by
  have hz : A*(T-2*(0:ℝ))≠0 := by
    simpa only [mul_zero,sub_zero] using mul_ne_zero hA.ne' hT.ne'
  have hR : ContinuousAt (fun s : ℝ => r+1/(A*(T-2*s))) 0 := by
    fun_prop (disch := assumption)
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, Y s≤r+1/(A*(T-2*s)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ)<T/3 by positivity)).filter_mono nhdsWithin_le_nhds] with s hs hsT
    have hs0 : 0<s := hs
    have hs2 : 0<T-2*s := by linarith
    by_cases hr : r<Y s
    · have hb := riccati_finite_interval (Y:=Y) (a:=s) (b:=T-s)
        (by linarith) hA
        (hc.mono (by intro x hx; exact ⟨le_trans hs0.le hx.1,by linarith [hx.2]⟩)) hr
        (by intro x hx; exact hd x ⟨lt_of_lt_of_le hs0 hx.1,by linarith [hx.2]⟩)
      convert hb.le using 1
      ring
    · exact (le_of_not_gt hr).trans (le_add_of_nonneg_right (by positivity))
  have hh := le_of_tendsto_of_tendsto
    (h0.tendsto.mono_left nhdsWithin_le_nhds)
    (hR.tendsto.mono_left nhdsWithin_le_nhds) hle
  simpa only [mul_zero,sub_zero] using hh

end RegularPointCoordinates

end OAI
