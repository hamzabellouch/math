import OAI.Analysis.CircleDomains.Uniformization.ExteriorDiskNormalization

namespace OAI

/-! An explicit holomorphic chart from the upper half-disk to the
exterior side of a round boundary. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def unitExteriorBoundaryChart (p z : ℂ) : ℂ := -p/halfPlaneDisk z

def roundExteriorBoundaryChart (c : ℂ) (r : ℝ) (p z : ℂ) : ℂ :=
  c+(r:ℂ)*unitExteriorBoundaryChart p z

lemma unitExteriorBoundaryChart_zero (p : ℂ) : unitExteriorBoundaryChart p 0=p := by
  simp [unitExteriorBoundaryChart,halfPlaneDisk]

lemma cayley_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖<1) : halfPlaneDisk z≠0 := by
  apply div_ne_zero
  · intro he
    have := congrArg norm (sub_eq_zero.mp he)
    simp only [norm_I] at this
    linarith
  · intro he
    have : z = -I := eq_neg_of_add_eq_zero_left he
    rw [this,norm_neg,norm_I] at hz
    exact (lt_irrefl (1:ℝ)) hz

lemma cayley_den_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖<1) : z+I≠0 := by
  intro he
  have : z = -I := eq_neg_of_add_eq_zero_left he
  rw [this,norm_neg,norm_I] at hz
  exact (lt_irrefl (1:ℝ)) hz

lemma differentiableAt_unitExteriorBoundaryChart (p : ℂ) {z : ℂ} (hz : ‖z‖<1) :
    DifferentiableAt ℂ (unitExteriorBoundaryChart p) z :=
  (differentiableAt_const (-p)).div
    (differentiableAt_halfPlaneDisk (cayley_den_ne_zero_of_norm_lt_one hz))
    (cayley_ne_zero_of_norm_lt_one hz)

lemma unitExteriorBoundaryChart_norm_gt_one {p z : ℂ} (hp : ‖p‖=1)
    (hz : ‖z‖<1) (hi : 0<z.im) : 1<‖unitExteriorBoundaryChart p z‖ := by
  rw [unitExteriorBoundaryChart,norm_div,norm_neg,hp]
  exact (lt_div_iff₀ (norm_pos_iff.mpr (cayley_ne_zero_of_norm_lt_one hz))).mpr
    (by simpa only [one_mul] using halfPlaneDisk_norm_lt hi)

lemma unitExteriorBoundaryChart_norm_eq_one {p z : ℂ} (hp : ‖p‖=1)
    (hi : z.im=0) : ‖unitExteriorBoundaryChart p z‖=1 := by
  rw [unitExteriorBoundaryChart,norm_div,norm_neg,hp,halfPlaneDisk_norm_eq hi,div_one]

lemma roundExteriorBoundaryChart_norm {c p z : ℂ} {r : ℝ} (hr : 0<r) :
    ‖roundExteriorBoundaryChart c r p z-c‖=r*‖unitExteriorBoundaryChart p z‖ := by
  simp only [roundExteriorBoundaryChart,add_sub_cancel_left,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hr]

lemma roundExteriorBoundaryChart_differentiable (c p : ℂ) (r : ℝ) {z : ℂ}
    (hz : ‖z‖<1) : DifferentiableAt ℂ (roundExteriorBoundaryChart c r p) z :=
  (differentiableAt_const c).add ((differentiableAt_unitExteriorBoundaryChart p hz).const_mul _)

lemma roundExteriorBoundaryChart_exterior {c p z : ℂ} {r : ℝ} (hr : 0<r)
    (hp : ‖p‖=1) (hz : ‖z‖<1) (hi : 0<z.im) :
    roundExteriorBoundaryChart c r p z∉closedBall c r := by
  rw [mem_closedBall_iff_norm,roundExteriorBoundaryChart_norm hr]
  exact not_le.mpr (by nlinarith [unitExteriorBoundaryChart_norm_gt_one hp hz hi])

lemma roundExteriorBoundaryChart_boundary {c p z : ℂ} {r : ℝ} (hr : 0<r)
    (hp : ‖p‖=1) (hi : z.im=0) : roundExteriorBoundaryChart c r p z∈sphere c r := by
  rw [mem_sphere_iff_norm,roundExteriorBoundaryChart_norm hr,
    unitExteriorBoundaryChart_norm_eq_one hp hi,mul_one]

end CircleDomainRigidity

end

end OAI
