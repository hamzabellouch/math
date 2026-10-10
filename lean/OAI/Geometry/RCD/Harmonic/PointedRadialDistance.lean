import OAI.Geometry.RCD.Metric.MeasuredApproximation

namespace OAI

/-! # Radial control and inner-ball comparison for the prescribed maps -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_radial_distance {n : ℕ} {p : X} {r S ε : ℝ}
    (hr : 0<r) (hS : 0≤S) {v : X → Euclidean n}
    (hv : IsPointedApproximation p 0 r S ε v)
    {x : X} (hx : dist x p≤S*r) :
    |‖v x‖-dist x p/r|≤2*ε := by
  have hd := abs_le.mp (hv.2.1 x p hx (by simpa only [dist_self] using mul_nonneg hS hr.le))
  have hp : ‖v p‖≤ε := by simpa only [dist_zero_right] using hv.1
  have h₁ := dist_triangle (v x) (v p) 0
  have h₂ := dist_triangle (v x) 0 (v p)
  simp only [dist_zero_right,dist_zero_left] at h₁ h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem pointed_ball_discrepancy_in_shell {n : ℕ} {p : X} {r S ε ρ δ : ℝ}
    (hr : 0<r) (hS : 0≤S) (hsmall : 2*ε<δ)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    {x : X} (hx : x∈ball p (S*r))
    (hdis : (x∈ball p (ρ*r) ∧ v x∉ball 0 ρ) ∨
      (x∉ball p (ρ*r) ∧ v x∈ball 0 ρ)) :
    v x∈closedBall 0 (ρ+δ) \ ball 0 (ρ-δ) := by
  have hd := abs_le.mp (pointed_radial_distance hr hS hv hx.le)
  have hinner : x∈ball p (ρ*r) ↔ dist x p/r<ρ := by
    rw [mem_ball,div_lt_iff₀ hr]
  have hout : x∉ball p (ρ*r) ↔ ρ≤dist x p/r := by
    rw [hinner,not_lt]
  rcases hdis with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have ha' := hinner.mp ha
    have hb' : ρ≤‖v x‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hb
    exact ⟨by simpa only [mem_closedBall,dist_zero_right] using (show ‖v x‖≤ρ+δ by linarith),
      by simpa only [mem_ball,dist_zero_right,not_lt] using (show ρ-δ≤‖v x‖ by linarith)⟩
  · have ha' := hout.mp ha
    have hb' : ‖v x‖<ρ := by simpa only [mem_ball,dist_zero_right] using hb
    have hδ : 0<δ := by
      have hε := (hv.1.trans' dist_nonneg)
      linarith
    exact ⟨by simpa only [mem_closedBall,dist_zero_right] using (show ‖v x‖≤ρ+δ by linarith),
      by simpa only [mem_ball,dist_zero_right,not_lt] using (show ρ-δ≤‖v x‖ by linarith)⟩

end RegularPointCoordinates

end

end OAI
