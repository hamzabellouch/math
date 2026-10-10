import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.Space

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def atomicCellScale (y : Space) : ℝ := ‖y‖/100000

lemma atomicCellScale_nonneg (y : Space) : 0 ≤ atomicCellScale y := div_nonneg (norm_nonneg _) (by norm_num)
lemma atomicCellScale_pos {y : Space} (hy : y≠0) : 0 < atomicCellScale y := div_pos (norm_pos_iff.mpr hy) (by norm_num)
lemma atomicCellScale_norm (y : Space) : 100000*atomicCellScale y=‖y‖ := by unfold atomicCellScale; ring

lemma atomicCellScale_comparable {y z : Space} (h : ‖z-y‖ ≤ 82*atomicCellScale y) :
    atomicCellScale y/2 ≤ atomicCellScale z ∧ atomicCellScale z ≤ 2*atomicCellScale y := by
  have h1 : ‖z‖ ≤ ‖z-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (z-y) y
  have h2 : ‖y‖ ≤ ‖z-y‖+‖z‖ := by
    have h := norm_add_le (y-z) z
    simpa only [sub_add_cancel,norm_sub_rev y z] using h
  have hy := atomicCellScale_nonneg y
  have he := atomicCellScale_norm y
  have hz := atomicCellScale_norm z
  constructor <;> linarith

lemma atomicCellScale_near_nonzero {y z : Space} (hy : y≠0)
    (h : ‖z-y‖ ≤ 82*atomicCellScale y) : z≠0 := by
  have hp := atomicCellScale_pos hy
  have H := (atomicCellScale_comparable h).1
  intro hz
  subst z
  have hzero : atomicCellScale (0:Space)=0 := by norm_num [atomicCellScale]
  rw [hzero] at H
  linarith

lemma atomicCellScale_nucleus_far (y : Space) : 4*atomicCellScale y ≤ ‖(0:Space)-y‖ := by
  rw [zero_sub,norm_neg]
  have h := atomicCellScale_norm y
  have hz := atomicCellScale_nonneg y
  linarith

lemma exists_atomic_patch_mesh : ∃ t : Finset Space,
    (∀ z∈t, ‖z‖ ≤ 80) ∧ (∀ w : Space, ‖w‖ ≤ 80 → ∃ z∈t, ‖w-z‖ < 1/4) := by
  let B := Metric.closedBall (0:Space) 80
  have hc : IsCompact B := isCompact_closedBall _ _
  have hcover : B ⊆ ⋃ z : B, Metric.ball z.val (1/4) := by
    intro w hw
    exact Set.mem_iUnion.mpr ⟨⟨w,hw⟩,by simp⟩
  obtain ⟨t,ht⟩ := hc.elim_finite_subcover (fun z : B => Metric.ball z.val (1/4))
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨t.image Subtype.val,?_,?_⟩
  · intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    simpa only [B,Metric.mem_closedBall,dist_zero_right] using v.property
  · intro w hw
    have hwB : w∈B := by simpa only [B,Metric.mem_closedBall,dist_zero_right] using hw
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp (ht hwB)
    obtain ⟨hzt,hzw⟩ := Set.mem_iUnion.mp hz
    refine ⟨z.val,Finset.mem_image.mpr ⟨z,hzt,rfl⟩,?_⟩
    simpa only [Metric.mem_ball,dist_eq_norm] using hzw

def atomicPatchMesh : Finset Space := Classical.choose exists_atomic_patch_mesh
lemma atomicPatchMesh_norm (z : Space) (hz : z∈atomicPatchMesh) : ‖z‖ ≤ 80 :=
  (Classical.choose_spec exists_atomic_patch_mesh).1 z hz
lemma atomicPatchMesh_covers (w : Space) (hw : ‖w‖ ≤ 80) :
    ∃ z∈atomicPatchMesh, ‖w-z‖ < 1/4 := (Classical.choose_spec exists_atomic_patch_mesh).2 w hw

def atomicMeshCenter (y z : Space) : Space := y+atomicCellScale y • z

lemma atomicMeshCenter_distance (y z : Space) (hz : z∈atomicPatchMesh) :
    ‖atomicMeshCenter y z-y‖ ≤ 80*atomicCellScale y := by
  simp only [atomicMeshCenter,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg (atomicCellScale_nonneg y)]
  nlinarith [atomicPatchMesh_norm z hz,atomicCellScale_nonneg y]

lemma atomicMeshCenter_comparable (y z : Space) (hz : z∈atomicPatchMesh) :
    atomicCellScale y/2 ≤ atomicCellScale (atomicMeshCenter y z) ∧
      atomicCellScale (atomicMeshCenter y z) ≤ 2*atomicCellScale y :=
  atomicCellScale_comparable (by nlinarith [atomicMeshCenter_distance y z hz,atomicCellScale_nonneg y])

theorem atomicMesh_cover {y : Space} (hy : y≠0) (w : Space)
    (hw : ‖w-y‖ ≤ 80*atomicCellScale y) :
    ∃ z∈atomicPatchMesh, ‖w-atomicMeshCenter y z‖ ≤ atomicCellScale (atomicMeshCenter y z) := by
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have hnorm : ‖a⁻¹ • (w-y)‖ ≤ 80 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
    exact (inv_mul_le_iff₀ ha).2 (by simpa only [mul_comm] using hw)
  obtain ⟨z,hz,hclose⟩ := atomicPatchMesh_covers (a⁻¹ • (w-y)) hnorm
  have he : w-atomicMeshCenter y z = a • (a⁻¹ • (w-y)-z) := by
    simp only [smul_sub,smul_smul,mul_inv_cancel₀ ha.ne',one_smul,atomicMeshCenter]
    change w-(y+a • z)=w-y-a • z
    abel
  have hdist : ‖w-atomicMeshCenter y z‖ < a/4 := by
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    nlinarith
  refine ⟨z,hz,?_⟩
  have H := (atomicMeshCenter_comparable y z hz).1
  dsimp [a] at hdist
  linarith [atomicCellScale_nonneg y]

lemma atomic_raw_exclusion_subset {z v : Space}
    (hv : ‖v-z‖ ≤ 2*atomicCellScale z) :
    {w : Space | 40*atomicCellScale v ≤ ‖w-v‖} ⊆ {w : Space | 4*atomicCellScale z ≤ ‖w-z‖} := by
  have H := (atomicCellScale_comparable (show ‖v-z‖ ≤ 82*atomicCellScale z by nlinarith [atomicCellScale_nonneg z])).1
  intro w hw
  change 40*atomicCellScale v ≤ ‖w-v‖ at hw
  change 4*atomicCellScale z ≤ ‖w-z‖
  have ht : ‖w-v‖ ≤ ‖w-z‖+‖v-z‖ := by
    simpa only [dist_eq_norm,norm_sub_rev z v] using dist_triangle w z v
  linarith [atomicCellScale_nonneg z]

end Coulomb
end

end
end

end OAI
