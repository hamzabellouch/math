import OAI.Analysis.CircleDomains.Selection.LocalizedSmallPerturbation

namespace OAI

/-! A smooth map whose value and differential vanish at the origin has
a compactly supported small ambient extension on a sufficiently small disk. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_smooth_local_error_extension {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (h0 : (0:ℂ)∈U) (hf : ContDiffOn ℝ ∞ f U)
    (hf0 : f 0=0) (hdf0 : fderiv ℝ f 0=0) {ε : ℝ} (hε : 0<ε) :
    ∃r:ℝ,0<r ∧ 2*r<ε ∧ ∃H : ℂ ≃ₜ ℂ,
      ContDiff ℝ ∞ (H : ℂ → ℂ) ∧ ContDiff ℝ ∞ (H.symm : ℂ → ℂ) ∧
      (∀z∈closedBall 0 r,H z=z+f z) ∧ (∀z,2*r≤‖z‖ → H z=z) := by
  obtain ⟨B,hB0,hB⟩ := exists_planeUnitBump_derivative_bound
  let d := 1/(2*(1+2*B))
  have hd : 0<d := by dsimp [d];positivity
  have hsmall : d*(1+2*B)<1 := by
    have hpos : 0<1+2*B := by positivity
    dsimp [d]
    field_simp
    nlinarith
  have hc : ContinuousAt (fun z => ‖fderiv ℝ f z‖) 0 :=
    ((hf 0 h0).contDiffAt (hU.mem_nhds h0)).continuousAt_fderiv (by simp) |>.norm
  have hevent : ∀ᶠ z in 𝓝 (0:ℂ), z∈U ∧ ‖fderiv ℝ f z‖<d := by
    have hn : ‖fderiv ℝ f 0‖<d := by rw [hdf0,norm_zero];exact hd
    have hmem : ∀ᶠ z in 𝓝 (0:ℂ), z∈U := hU.mem_nhds h0
    exact hmem.and (hc.eventually (gt_mem_nhds hn))
  obtain ⟨R,hR,hsubR⟩ := Metric.eventually_nhds_iff.mp hevent
  let r := min R ε/4
  have hr : 0<r := by dsimp [r];positivity
  have hrR : 2*r<R := by dsimp [r];linarith [min_le_left R ε]
  have hrε : 2*r<ε := by dsimp [r];linarith [min_le_right R ε]
  have hball (z : ℂ) (hz : z∈closedBall 0 (2*r)) : z∈U ∧ ‖fderiv ℝ f z‖<d := by
    apply hsubR
    rw [dist_zero_right]
    exact (mem_closedBall_zero_iff.mp hz).trans_lt hrR
  have hsub : closedBall (0:ℂ) (2*r)⊆U := fun z hz => (hball z hz).1
  have hval : ∀z∈closedBall (0:ℂ) (2*r),‖f z‖≤2*r*d := by
    intro z hz
    have hn := (convex_closedBall (0:ℂ) (2*r)).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw => ((hf w (hsub hw)).contDiffAt (hU.mem_nhds (hsub hw))).differentiableAt (by simp))
      (fun w hw => (hball w hw).2.le)
      (mem_closedBall_self (by positivity)) hz
    rw [hf0,sub_zero,sub_zero] at hn
    exact hn.trans (by nlinarith [mem_closedBall_zero_iff.mp hz])
  obtain ⟨H,hHs,hHi,hHin,hHout⟩ := exists_localized_smooth_perturbation hr hB0 hd.le hsmall hB
    hU hsub hf (fun z hz => (hball z hz).2.le) hval
  exact ⟨r,hr,hrε,H,hHs,hHi,hHin,hHout⟩

end CircleDomainRigidity

end

end OAI
