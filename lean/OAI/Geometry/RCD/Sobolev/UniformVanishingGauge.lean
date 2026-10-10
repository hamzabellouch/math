import OAI.Geometry.RCD.Sobolev.UniformCenteredConvergence

namespace OAI

/-! # Removing a uniformly vanishing scalar gauge -/

open Filter
open scoped Topology
namespace RegularPointCoordinates

theorem uniform_of_sub_vanishing {Y : Type*} {f : ℕ → Y → ℝ} {g : Y → ℝ}
    {c : ℕ → ℝ} (h : TendstoUniformly (fun k x => f k x-c k) g atTop)
    (hc : Tendsto c atTop (𝓝 0)) : TendstoUniformly f g atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hh := hc.eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < ε/2))
  filter_upwards [(Metric.tendstoUniformly_iff.mp h) (ε/2) (by linarith),hh] with k hk hc'
  intro x
  have hx := hk x
  change dist (c k) 0 < ε/2 at hc'
  rw [Real.dist_eq,sub_zero] at hc'
  rw [Real.dist_eq] at hx ⊢
  rcases abs_lt.mp hx with ⟨hx₁,hx₂⟩
  rcases abs_lt.mp hc' with ⟨hc₁,hc₂⟩
  apply abs_lt.mpr
  constructor <;> linarith

end RegularPointCoordinates

end OAI
