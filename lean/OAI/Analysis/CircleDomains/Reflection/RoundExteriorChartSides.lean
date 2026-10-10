import OAI.Analysis.CircleDomains.Reflection.RoundExteriorBoundaryInjectivity

namespace OAI

/-! The circular boundary chart has the exact two sides: its closed
lower half maps into the closed disk, and its strict upper half maps
outside it. -/
open Set Function Metric Complex
noncomputable section
namespace CircleDomainRigidity

lemma unitExteriorBoundaryChart_norm_le_one {p z : ℂ} (hp : ‖p‖=1)
    (hz : ‖z‖<1) (hi : z.im≤0) : ‖unitExteriorBoundaryChart p z‖≤1 := by
  have hzm : z-I≠0 := by
    intro he
    have hn := congrArg norm (sub_eq_zero.mp he)
    rw [norm_I] at hn
    linarith
  have hn := halfPlaneDisk_normSq z
  simp only [←Complex.sq_norm] at hn
  have hle : ‖z+I‖≤‖z-I‖ := by
    nlinarith [norm_nonneg (z+I),norm_nonneg (z-I)]
  rw [unitExteriorBoundaryChart,norm_div,norm_neg,hp,halfPlaneDisk,norm_div,one_div_div]
  exact (div_le_one (norm_pos_iff.mpr hzm)).mpr hle

lemma roundExteriorBoundaryChart_mem_closedBall {c p z : ℂ} {r : ℝ}
    (hr : 0<r) (hp : ‖p‖=1) (hz : ‖z‖<1) (hi : z.im≤0) :
    roundExteriorBoundaryChart c r p z∈closedBall c r := by
  rw [mem_closedBall_iff_norm,roundExteriorBoundaryChart_norm hr]
  have := unitExteriorBoundaryChart_norm_le_one hp hz hi
  nlinarith

lemma roundExteriorBoundaryChart_outside_iff {c p z : ℂ} {r : ℝ}
    (hr : 0<r) (hp : ‖p‖=1) (hz : ‖z‖<1) :
    roundExteriorBoundaryChart c r p z∉closedBall c r ↔ 0<z.im := by
  constructor
  · intro h
    by_contra hneg
    exact h (roundExteriorBoundaryChart_mem_closedBall hr hp hz (le_of_not_gt hneg))
  · exact roundExteriorBoundaryChart_exterior hr hp hz

end CircleDomainRigidity

end

end OAI
