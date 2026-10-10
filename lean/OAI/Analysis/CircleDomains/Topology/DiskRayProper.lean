import OAI.Analysis.CircleDomains.Topology.DiskRayLift

namespace OAI

/-! Uniform properness and angular bounds on every bounded-depth strip
for the lifted compact disk-arc family. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem compact_disk_rays_depth_escape
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (Y : ℝ) :
    ∃ c : PathTime, 0 < c ∧ c < 1 ∧
      ∀ γ ∈ K, ∀ t : DiskRayTime, c ≤ t.val → Y < diskRayDepth γ t := by
  obtain ⟨c, hc0, hc1, htail⟩ := compact_disk_rays_uniform_tail K hK
    (fun γ hγ => (hKS hγ).2.2.1) (Real.exp_pos (-Y))
  refine ⟨c, hc0, hc1, fun γ hγ t ht => ?_⟩
  have hp : 0 < ‖γ t.val‖ := norm_pos_iff.mpr
    (diskRay_nonzero γ (hKS hγ).1 (hKS hγ).2.2.1 t)
  have hh : Real.log ‖γ t.val‖ < -Y := (Real.log_lt_iff_lt_exp hp).mpr (htail γ hγ t.val ht)
  change Y < -Real.log ‖γ t.val‖
  linarith

theorem compact_disk_rays_angle_bound_on_strip
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (Y : ℝ) :
    ∃ M : ℝ, ∀ γ : K, ∀ t : DiskRayTime, diskRayDepth γ.val t ≤ Y →
      |diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 t| ≤ M := by
  obtain ⟨c, hc, M, hc0, htime, hM⟩ :=
    compact_disk_rays_initial_angle_bound K hK hKS (Real.exp_pos (-Y))
  refine ⟨M, fun γ t ht => ?_⟩
  have hp : 0 < ‖γ.val t.val‖ := norm_pos_iff.mpr
    (diskRay_nonzero γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 t)
  have hnorm : Real.exp (-Y) ≤ ‖γ.val t.val‖ := by
    apply (Real.le_log_iff_exp_le hp).mp
    change -Real.log ‖γ.val t.val‖ ≤ Y at ht
    linarith
  have htc := htime γ.val γ.property t.val hnorm
  have hcp : (0 : ℝ) < c := hc0
  let u : unitInterval := ⟨(t.val : ℝ) / (c : ℝ),
    div_nonneg t.val.property.1 hcp.le, (div_le_one hcp).mpr htc.le⟩
  have hut : u * c = t.val := by
    apply Subtype.ext
    exact div_mul_cancel₀ _ hcp.ne'
  have he : (⟨u * c, unitInterval.mul_le_right.trans_lt hc⟩ : DiskRayTime) = t :=
    Subtype.ext hut
  have ha := diskRayAngle_mul_prefix γ.val (hKS γ.property).1
    (hKS γ.property).2.2.1 (⟨c, hc⟩ : DiskRayTime) u
  have hat : diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 t =
      realCirclePathLift (initialArcAngles puncturedArgument γ.val
        (hKS γ.property).1 (hKS γ.property).2.2.1 c hc) u := by
    simpa only [he] using ha
  exact (congrArg abs hat).symm ▸ hM γ u

theorem diskRayDepth_nonneg {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet)
    (t : DiskRayTime) : 0 ≤ diskRayDepth γ t := by
  have hp : 0 < ‖γ t.val‖ := norm_pos_iff.mpr (diskRay_nonzero γ hγ.1 hγ.2.2.1 t)
  have hle := (Real.log_le_iff_le_exp hp).mpr
    (show ‖γ t.val‖ ≤ Real.exp 0 by simpa only [Real.exp_zero] using diskTerminalArc_norm_le hγ t.val)
  exact neg_nonneg.mpr hle

end CircleDomainRigidity

end

end OAI
