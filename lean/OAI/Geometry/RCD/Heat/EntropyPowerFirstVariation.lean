import OAI.Geometry.RCD.Transport.HyperbolicChordLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-! # Entropy first variation from a differentiable lower entropy-power barrier

Only a one-sided bound and the derivative of the explicit barrier are used.
The entropy along the transport curve need not itself be differentiable.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem entropy_power_first_variation {E V v : ℝ → ℝ} {N D d M : ℝ}
    (hN : 0 < N) (hV0 : 0 < V 0) (hV : HasDerivAt V D 0)
    (hE0 : E 0 = -N*Real.log (V 0))
    (hp : ∀ᶠ t in 𝓝[>] (0:ℝ), V t ≤ Real.exp (-E t/N))
    (hv : ∀ᶠ t in 𝓝[>] (0:ℝ), v t ≤ (E t-E 0)/t+t*M)
    (hd : Tendsto v (𝓝[>] (0:ℝ)) (𝓝 d)) : d ≤ -N*(D/(V 0)) := by
  have hbar := (hV.log hV0.ne').const_mul (-N)
  have hlim : Tendsto (fun t : ℝ => (-N*Real.log (V t)-E 0)/t)
      (𝓝[>] (0:ℝ)) (𝓝 (-N*(D/(V 0)))) := by
    simpa only [slope_fun_def_field,←hE0,sub_zero] using
      hbar.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
  have hm : Tendsto (fun t : ℝ => t*M) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun t : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 0)).mul_const M)
  have hl : Tendsto (fun t : ℝ => (-N*Real.log (V t)-E 0)/t+t*M)
      (𝓝[>] (0:ℝ)) (𝓝 (-N*(D/(V 0)))) := by simpa using hlim.add hm
  apply le_of_tendsto_of_tendsto hd hl
  have hpos : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < V t :=
    (hV.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hV0)
  filter_upwards [hp,hv,hpos,self_mem_nhdsWithin] with t hp hv hpos ht
  have hh := Real.log_le_log hpos hp
  rw [Real.log_exp] at hh
  have he : E t ≤ -N*Real.log (V t) := by
    have hmul := (le_div_iff₀ hN).mp hh
    nlinarith only [hmul]
  exact hv.trans (add_le_add
    (div_le_div_of_nonneg_right (sub_le_sub_right he (E 0)) ht.le) le_rfl)

end RegularPointCoordinates

end

end OAI
