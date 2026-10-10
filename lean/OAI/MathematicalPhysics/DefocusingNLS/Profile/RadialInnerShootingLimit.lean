import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerShootingFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexBoundaryConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactSubsequence
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Uniform convergence of the actual nonlinear inner boundary jet on the shooting disk. -/

open Set Filter
namespace DefocusingNLS

theorem innerBoundaryRadius_lower : (3+7/10000 : ℝ) ≤ innerBoundaryRadius := by
  have hz : (27/10 : ℝ) ≤ (ProfileCertificate.centerZ : ℝ) := by
    norm_num [ProfileCertificate.centerZ]
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (ProfileCertificate.centerZ : ℝ) by linarith)
  have hs := Real.sqrt_nonneg (ProfileCertificate.centerZ : ℝ)
  have hl : (8/5 : ℝ) ≤ Real.sqrt (ProfileCertificate.centerZ : ℝ) := by nlinarith
  unfold innerBoundaryRadius
  linarith

theorem radialShootingInner_subsequence_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (w : ℕ → RadialShootingDisk) (w₀ : RadialShootingDisk)
    (hw : Tendsto w atTop (nhds w₀)) :
    Tendsto (fun i => radialShootingInnerBoundary (s i) (w i)) atTop
      (nhds (radialFreeInnerJet w₀ innerBoundaryRadius)) := by
  have hsn : Tendsto (fun i => s i+radialInnerShootingThreshold) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) hs.tendsto_atTop
  have hp : Tendsto (fun i => (radialShootingInnerData (s i) (w i)).p) atTop atTop := by
    simp only [radialShootingInnerData_p]
    exact tendsto_atTop_mono (fun i => by omega) hs.tendsto_atTop
  have hc : Tendsto (fun i => (radialShootingInnerData (s i) (w i)).c) atTop (nhds 6) := by
    simp only [radialShootingInnerData_c]
    have ht := ((tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (nhds 0)).comp hsn).const_sub 6
    simpa only [Function.comp_def,sub_zero] using ht
  have hbc : Continuous radialShootingB := by unfold radialShootingB; fun_prop
  have hb : Tendsto (fun i => (radialShootingInnerData (s i) (w i)).b) atTop
      (nhds (radialShootingB w₀)) := by
    simpa only [radialShootingInnerData_b] using! hbc.continuousAt.tendsto.comp hw
  have hlo : Tendsto (fun i => (radialShootingInnerData (s i) (w i)).lo) atTop
      (nhds ‖(radialFreeInnerJet w₀ innerBoundaryRadius).1‖) := by
    simpa only [radialShootingInnerData_lo] using!
      continuous_radialFreeInner_boundary.fst.norm.continuousAt.tendsto.comp hw
  obtain ⟨hb₀,hR₀,hu,hlu,hwidth,hshell⟩ := radialShooting_geometry w₀
  have hslt : radialShootingR w₀ < innerBoundaryRadius := by linarith [hshell.1]
  obtain ⟨hJ,hFI,hGI,hbound,_⟩ := radialFreeInnerJet_spec w₀
  have hconv := radial_coupled_complex_boundary_convergence innerBoundaryRadius (radialShootingR w₀)
    (radialShootingB w₀) innerBoundaryRadius_lower hu hR₀ hslt hwidth hb₀
    (fun r => (radialFreeInnerJet w₀ r).1) (fun r => (radialFreeInnerJet w₀ r).2)
    hJ.fst hJ.snd hFI hGI (fun r _ => hbound r)
    (fun i => radialShootingInnerData (s i) (w i)) (fun i => radialShootingInnerData_R (s i) (w i))
    (fun i => radialShootingInnerAmplitude (s i) (w i))
    (fun i => by simpa only [radialShootingInnerData_R] using
      radialShootingInnerAmplitude_spec (s i) (w i)) hp hc hb hlo
  simpa only [radialShootingInnerBoundary,radialShootingInnerComplex] using! hconv

theorem radialShootingInner_uniform_limit :
    TendstoUniformly radialShootingInnerBoundary
      (fun w => radialFreeInnerJet w innerBoundaryRadius) atTop := by
  classical
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  by_contra h
  obtain ⟨s,hs,w,w₀,hw,hbad⟩ := radial_compact_bad_subsequence
    (fun n w => dist (radialFreeInnerJet w innerBoundaryRadius) (radialShootingInnerBoundary n w) < ε) h
  have hI := radialShootingInner_subsequence_limit s hs w w₀ hw
  have hF := continuous_radialFreeInner_boundary.continuousAt.tendsto.comp hw
  have hd : Tendsto (fun i => dist (radialShootingInnerBoundary (s i) (w i))
      (radialFreeInnerJet (w i) innerBoundaryRadius)) atTop (nhds 0) := by
    simpa only [dist_self] using! hI.dist hF
  obtain ⟨i,hi⟩ := (hd.eventually (gt_mem_nhds hε)).exists
  exact hbad i (by simpa only [dist_comm] using hi)

end DefocusingNLS

end OAI
