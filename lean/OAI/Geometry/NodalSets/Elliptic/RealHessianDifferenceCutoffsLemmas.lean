import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas
import OAI.Geometry.NodalSets.Elliptic.RealCubeCutoffs

namespace OAI

noncomputable section

namespace Yau

open Set Filter
open scoped ContDiff Topology

theorem real_hessian_difference_cutoffs :
    ∃ eta chi : Jets.Coord → ℝ,
      ContDiff ℝ ∞ eta ∧ ContDiff ℝ ∞ chi ∧ HasCompactSupport eta ∧ HasCompactSupport chi ∧
      tsupport eta ⊆ interior (realCenteredCube 4 (3/8)) ∧
      tsupport chi ⊆ interior (realCenteredCube 4 (1/2)) ∧
      (∀ x, 0 ≤ eta x ∧ eta x ≤ 1) ∧ (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) ∧
      (∀ x ∈ realCenteredCube 4 (1/4), eta =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
      ∀ (i : Fin 4) (h : ℝ), |h| ≤ 1/32 → ∀ x ∈ tsupport eta,
        x ∈ interior (realCenteredCube 4 (1/2)) ∧
        x+Pi.single i h ∈ interior (realCenteredCube 4 (1/2)) ∧
        chi =ᶠ[𝓝 x] (fun _ ↦ 1) ∧ chi =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1) := by
  obtain ⟨eta,he,hec,hes,heb,he1⟩ := real_cube_smooth_cutoff (1/4) (5/16) (by norm_num)
  obtain ⟨chi,hc,hcc,hcs,hcb,hc1⟩ := real_cube_smooth_cutoff (7/16) (15/32) (by norm_num)
  refine ⟨eta,chi,he,hc,hec,hcc,hes.trans (realCenteredCube_subset_interior (by norm_num)),
    hcs.trans (realCenteredCube_subset_interior (by norm_num)),heb,hcb,he1,?_⟩
  intro i h hh x hx
  have hxsmall := hes hx
  have hxouter : x ∈ realCenteredCube 4 (7/16) := realCenteredCube_mono (by norm_num) hxsmall
  have hxt : x+Pi.single i h ∈ realCenteredCube 4 (7/16) := by
    apply realCenteredCube_shift i (h := -h) (r := 5/16)
      (by simpa only [abs_neg] using (show |h| ≤ (7/16:ℝ)-5/16 by linarith))
    simpa only [Pi.single_neg,add_neg_cancel_right] using hxsmall
  exact ⟨realCenteredCube_subset_interior (by norm_num) hxouter,
    realCenteredCube_subset_interior (by norm_num) hxt,hc1 x hxouter,hc1 _ hxt⟩

theorem real_nested_difference_cutoffs (R r : ℝ) (hr : r < R) :
    ∃ eta chi : Jets.Coord → ℝ,
      ContDiff ℝ ∞ eta ∧ ContDiff ℝ ∞ chi ∧ HasCompactSupport eta ∧ HasCompactSupport chi ∧
      tsupport eta ⊆ interior (realCenteredCube 4 ((r+R)/2)) ∧
      tsupport chi ⊆ interior (realCenteredCube 4 R) ∧
      (∀ x, 0 ≤ eta x ∧ eta x ≤ 1) ∧ (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) ∧
      (∀ x ∈ realCenteredCube 4 r, eta =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
      ∀ (i : Fin 4) (h : ℝ), |h| ≤ (R-r)/8 → ∀ x ∈ tsupport eta,
        x ∈ interior (realCenteredCube 4 R) ∧
        x+Pi.single i h ∈ interior (realCenteredCube 4 R) ∧
        chi =ᶠ[𝓝 x] (fun _ ↦ 1) ∧ chi =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1) := by
  obtain ⟨eta,he,hec,hes,heb,he1⟩ := real_cube_smooth_cutoff r ((3*r+R)/4) (by linarith)
  obtain ⟨chi,hc,hcc,hcs,hcb,hc1⟩ := real_cube_smooth_cutoff ((r+3*R)/4) ((r+7*R)/8) (by linarith)
  refine ⟨eta,chi,he,hc,hec,hcc,hes.trans (realCenteredCube_subset_interior (by linarith)),
    hcs.trans (realCenteredCube_subset_interior (by linarith)),heb,hcb,he1,?_⟩
  intro i h hh x hx
  have hxsmall := hes hx
  have hxouter : x ∈ realCenteredCube 4 ((r+3*R)/4) := realCenteredCube_mono (by linarith) hxsmall
  have hxt : x+Pi.single i h ∈ realCenteredCube 4 ((r+3*R)/4) := by
    apply realCenteredCube_shift i (h := -h) (r := (3*r+R)/4)
      (by simpa only [abs_neg] using (show |h| ≤ ((r+3*R)/4)-(3*r+R)/4 by linarith))
    simpa only [Pi.single_neg,add_neg_cancel_right] using hxsmall
  exact ⟨realCenteredCube_subset_interior (by linarith) hxouter,
    realCenteredCube_subset_interior (by linarith) hxt,hc1 x hxouter,hc1 _ hxt⟩

end Yau

end

end OAI
