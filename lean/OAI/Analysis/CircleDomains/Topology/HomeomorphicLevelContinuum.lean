import OAI.Analysis.CircleDomains.Selection.FirstExitCuts
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Initial pieces of actual horizontal inverse lines provide compact
level continua from the centre to the boundary of any closed disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem homeomorphic_level_continuum (φ : ℂ ≃ₜ ℂ) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ K : Set ℂ, IsCompact K ∧ IsConnected K ∧ x ∈ K ∧
      K ⊆ closedBall x r ∧ (∀ y ∈ K, (φ y).im = (φ x).im) ∧
      (K ∩ sphere x r).Nonempty := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x r).image φ.continuous).isBounded.subset_ball 0
  let q : ℂ := ⟨max B 0+1, (φ x).im⟩
  have hq : φ.symm q ∉ closedBall x r := by
    intro h
    have hb : ‖q‖ < B := by
      have hh := hB (mem_image_of_mem φ h)
      simpa only [φ.apply_symm_apply, mem_ball, dist_zero_right] using hh
    have hle : max B 0+1 ≤ ‖q‖ := Complex.re_le_norm q
    linarith [le_max_left B 0]
  let γ : C(PathTime, ℂ) := ⟨fun t => φ.symm (φ x+(t : ℝ) • (q-φ x)), by fun_prop⟩
  have hstart : γ ⊥ = x := by simp [γ]
  have hstop : γ ⊤ ∉ ball x r := by
    have he : γ ⊤ = φ.symm q := by simp [γ]
    rw [he]
    exact fun h => hq (ball_subset_closedBall h)
  let τ := firstExitTime γ (ball x r)
  have hstartB : γ ⊥ ∈ ball x r := hstart ▸ mem_ball_self hr
  have hboundary : γ τ ∈ sphere x r := by
    have h := firstExit_frontier γ isOpen_ball hstartB hstop
    simpa only [frontier_ball x hr.ne'] using h
  let K := γ '' Iic τ
  have hc : IsConnected (Iic τ : Set PathTime) :=
    ⟨⟨⊥, mem_Iic.mpr bot_le⟩, isPreconnected_Iic⟩
  refine ⟨K, isClosed_Iic.isCompact.image γ.continuous, hc.image _ γ.continuous.continuousOn,
    ?_, ?_, ?_, ?_⟩
  · exact ⟨⊥, mem_Iic.mpr bot_le, hstart⟩
  · rintro y ⟨t, ht, rfl⟩
    have hh := firstExit_initial_segment γ isOpen_ball hstartB hstop ht
    simpa only [closure_ball x hr.ne'] using hh
  · rintro y ⟨t, ht, rfl⟩
    simp [γ, q, Complex.add_im, Complex.sub_im]
  · exact ⟨γ τ, ⟨τ, mem_Iic.mpr le_rfl, rfl⟩, hboundary⟩

end CircleDomainRigidity

end

end OAI
