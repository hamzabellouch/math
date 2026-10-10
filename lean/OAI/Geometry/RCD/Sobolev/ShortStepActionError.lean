import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace OAI

/-! # Choosing a short final heat step with arbitrarily small action error -/

open Set Filter
open scoped Topology
namespace RegularPointCoordinates

theorem short_step_action_parameters {d D T η : ℝ} (hT : 0 < T) (hη : 0 < η) :
    ∃ s r : ℝ, 0 < s ∧ s < T ∧ 0 < r ∧ r < 1 ∧
      d^2/(2*s)+2*D*r^2/(T-s) < d^2/(2*T)+η := by
  have hc : ContinuousAt (fun s : ℝ => d^2/(2*s)) T := by
    fun_prop (disch := positivity)
  have hs : ∀ᶠ s in 𝓝[<] T, 0 < s ∧ s < T ∧ d^2/(2*s) < d^2/(2*T)+η/2 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hT),self_mem_nhdsWithin,
      hc.continuousWithinAt.tendsto.eventually (gt_mem_nhds (by linarith :
        d^2/(2*T) < d^2/(2*T)+η/2))] with s hs hsT hcost
    exact ⟨hs,hsT,hcost⟩
  obtain ⟨s,hs,hsT,hcost⟩ := hs.exists
  have hc' : ContinuousAt (fun r : ℝ => 2*D*r^2/(T-s)) 0 := by
    fun_prop (disch := linarith)
  have hr : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r ∧ r < 1 ∧ 2*D*r^2/(T-s) < η/2 := by
    have hh : Tendsto (fun r : ℝ => 2*D*r^2/(T-s)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_div] using
        hc'.continuousWithinAt.tendsto (s := Ioi (0:ℝ))
    have he := hh.eventually (gt_mem_nhds (half_pos hη))
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),he] with r hr hr1 he
    exact ⟨hr,hr1,he⟩
  obtain ⟨r,hr,hr1,he⟩ := hr.exists
  exact ⟨s,r,hs,hsT,hr,hr1,by linarith⟩

end RegularPointCoordinates

end OAI
