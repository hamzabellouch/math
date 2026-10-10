import OAI.Analysis.CircleDomains.Topology.HalfPlaneDiskInverse
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace OAI

/-! Holomorphic Cayley coordinates and the exact strict side and boundary
relations used to turn circle reflection into real-axis reflection. -/
open Set Function Complex
noncomputable section
namespace CircleDomainRigidity

lemma differentiableAt_halfPlaneDisk {z : ℂ} (hz : z+I≠0) :
    DifferentiableAt ℂ halfPlaneDisk z :=
  (differentiableAt_id.sub_const I).div (differentiableAt_id.add_const I) hz

lemma differentiableAt_diskHalfPlane {z : ℂ} (hz : z≠1) :
    DifferentiableAt ℂ diskHalfPlane z :=
  ((differentiableAt_const I).mul ((differentiableAt_const 1).add differentiableAt_id)).div
    ((differentiableAt_const 1).sub differentiableAt_id) (diskHalfPlane_den_ne_zero hz)

lemma diskHalfPlane_pos {w : ℂ} (hn : ‖w‖<1) : 0<(diskHalfPlane w).im := by
  have hw : w≠1 := by intro he; simp [he] at hn
  have hh : ‖halfPlaneDisk (diskHalfPlane w)‖<1 := by
    rw [halfPlaneDisk_diskHalfPlane hw]
    exact hn
  rw [halfPlaneDisk,norm_div] at hh
  have hb : ‖diskHalfPlane w-I‖<‖diskHalfPlane w+I‖ := by
    exact (div_lt_one (norm_pos_iff.mpr (diskHalfPlane_add_I_ne_zero hw))).mp hh
  have hs := halfPlaneDisk_normSq (diskHalfPlane w)
  simp only [←Complex.sq_norm] at hs
  nlinarith [norm_nonneg (diskHalfPlane w-I)]

lemma diskHalfPlane_real {w : ℂ} (hw : w≠1) (hn : ‖w‖=1) :
    (diskHalfPlane w).im=0 := by
  have hh : ‖halfPlaneDisk (diskHalfPlane w)‖=1 := by
    rw [halfPlaneDisk_diskHalfPlane hw,hn]
  rw [halfPlaneDisk,norm_div] at hh
  have hb : ‖diskHalfPlane w-I‖=‖diskHalfPlane w+I‖ := by
    exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr (diskHalfPlane_add_I_ne_zero hw))).mp hh
  have hs := halfPlaneDisk_normSq (diskHalfPlane w)
  simp only [←Complex.sq_norm] at hs
  rw [hb] at hs
  linarith

lemma halfPlaneDisk_injOn_nonpole : InjOn halfPlaneDisk {z : ℂ | z+I≠0} := by
  intro z hz w hw he
  have hc := (div_eq_div_iff hz hw).mp he
  have h : (z-w)*(2*I)=0 := by
    calc
      _ = (z-I)*(w+I)-(w-I)*(z+I) := by ring
      _ = 0 := sub_eq_zero.mpr hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (by simp))

lemma diskHalfPlane_injOn_nonpole : InjOn diskHalfPlane {z : ℂ | z≠1} := by
  intro z hz w hw he
  calc
    z = halfPlaneDisk (diskHalfPlane z) := (halfPlaneDisk_diskHalfPlane hz).symm
    _ = halfPlaneDisk (diskHalfPlane w) := congrArg halfPlaneDisk he
    _ = w := halfPlaneDisk_diskHalfPlane hw

end CircleDomainRigidity

end

end OAI
