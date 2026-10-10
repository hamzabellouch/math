import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraph
import OAI.Combinatorics.TriangleRemoval.Process.TriangleThird
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph
import OAI.Combinatorics.TriangleRemoval.Queries.RecordedCallForest

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave.RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

def rootSet (_F : RecordedCallForest (triangleHypergraph G) c) : Finset (Fin n) := c.focus.biUnion id

def rootCount : ℕ := F.rootSet.card

def vertexCount : ℕ := F.rootCount + (F.size - 1)

lemma size_pos : 0 < F.size := lt_of_le_of_lt (Nat.zero_le _) F.root.isLt

lemma nonroot_pos (i : Fin F.size) (hi : i ≠ F.root) : 0 < i.val := by
  have hr := F.root_val
  have hn : i.val ≠ F.root.val := (Fin.ne_iff_vne _ _).mp hi
  omega

def birthIndex (i : Fin F.size) (hi : i ≠ F.root) : Fin F.vertexCount :=
  ⟨F.rootCount + (i.val - 1), by
    have his := i.isLt
    have hs := F.size_pos
    have hip := F.nonroot_pos i hi
    unfold vertexCount
    omega⟩

lemma birthIndex_nonroot (i : Fin F.size) (hi : i ≠ F.root) :
    F.rootCount ≤ (F.birthIndex i hi).val := Nat.le_add_right _ _

lemma birthIndex_injective (i j : Fin F.size) (hi : i ≠ F.root) (hj : j ≠ F.root)
    (he : F.birthIndex i hi = F.birthIndex j hj) : i = j := by
  have hi0 := F.nonroot_pos i hi
  have hj0 := F.nonroot_pos j hj
  have hh := congrArg Fin.val he
  change F.rootCount + (i.val - 1) = F.rootCount + (j.val - 1) at hh
  apply Fin.ext
  omega

lemma birthIndex_lt (i j : Fin F.size) (hi : i ≠ F.root) (hj : j ≠ F.root)
    (hij : i < j) : F.birthIndex i hi < F.birthIndex j hj := by
  have hi0 := F.nonroot_pos i hi
  change F.rootCount + (i.val - 1) < F.rootCount + (j.val - 1)
  change i.val < j.val at hij
  omega

def callIndex (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) : Fin F.size :=
  ⟨v.val - F.rootCount + 1, by
    have hs := F.size_pos
    have hvs := v.isLt
    unfold vertexCount at hvs
    omega⟩

lemma callIndex_nonroot (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.callIndex v hv ≠ F.root := by
  intro he
  have hh := congrArg Fin.val he
  change v.val - F.rootCount + 1 = F.root.val at hh
  rw [F.root_val] at hh
  omega

@[simp] lemma callIndex_birthIndex (i : Fin F.size) (hi : i ≠ F.root) :
    F.callIndex (F.birthIndex i hi) (F.birthIndex_nonroot i hi) = i := by
  apply Fin.ext
  change F.rootCount + (i.val - 1) - F.rootCount + 1 = i.val
  have hi0 := F.nonroot_pos i hi
  omega

@[simp] lemma birthIndex_callIndex (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.birthIndex (F.callIndex v hv) (F.callIndex_nonroot v hv) = v := by
  apply Fin.ext
  change F.rootCount + (v.val - F.rootCount + 1 - 1) = v.val
  omega

noncomputable def rootLabel (i : Fin F.rootCount) : Fin n :=
  ((F.rootSet.equivFin).symm i).val

lemma rootLabel_mem (i : Fin F.rootCount) : F.rootLabel i ∈ F.rootSet :=
  ((F.rootSet.equivFin).symm i).property

lemma rootLabel_injective : Function.Injective F.rootLabel := by
  intro i j he
  have hs : (F.rootSet.equivFin).symm i = (F.rootSet.equivFin).symm j := Subtype.ext he
  exact (F.rootSet.equivFin).symm.injective hs

lemma rootLabel_covers (x : Fin n) (hx : x ∈ F.rootSet) :
    ∃ i : Fin F.rootCount, F.rootLabel i = x := by
  refine ⟨F.rootSet.equivFin ⟨x,hx⟩,?_⟩
  exact congrArg Subtype.val (F.rootSet.equivFin.symm_apply_apply ⟨x,hx⟩)

noncomputable def vertexLabel (v : Fin F.vertexCount) : Fin n :=
  if hv : v.val < F.rootCount then F.rootLabel ⟨v.val,hv⟩
  else F.newVertex (F.callIndex v (Nat.le_of_not_gt hv)) (F.callIndex_nonroot v _)

lemma vertexLabel_root (v : Fin F.vertexCount) (hv : v.val < F.rootCount) :
    F.vertexLabel v = F.rootLabel ⟨v.val,hv⟩ := dite_eq_left hv

lemma vertexLabel_birth (i : Fin F.size) (hi : i ≠ F.root) :
    F.vertexLabel (F.birthIndex i hi) = F.newVertex i hi := by
  rw [vertexLabel,dite_eq_right (Nat.not_lt.mpr (F.birthIndex_nonroot i hi))]
  simp only [callIndex_birthIndex]

lemma vertexLabel_injective_roots : Set.InjOn F.vertexLabel {v | v.val < F.rootCount} := by
  intro v hv w hw he
  rw [F.vertexLabel_root v hv,F.vertexLabel_root w hw] at he
  exact Fin.ext (congrArg (fun i : Fin F.rootCount => i.val) (F.rootLabel_injective he))

lemma vertexLabel_covers (e : Finset (Fin n)) (he : e ∈ c.focus) (x : Fin n) (hx : x ∈ e) :
    ∃ v : Fin F.vertexCount, v.val < F.rootCount ∧ F.vertexLabel v = x := by
  have hxr : x ∈ F.rootSet := Finset.mem_biUnion.mpr ⟨e,he,hx⟩
  obtain ⟨i,hi⟩ := F.rootLabel_covers x hxr
  have hib : i.val < F.vertexCount := by
    have hh := i.isLt
    unfold vertexCount
    omega
  refine ⟨⟨i.val,hib⟩,i.isLt,?_⟩
  rw [F.vertexLabel_root _ i.isLt]
  exact hi

end SharpTerminalLeave.RecordedCallForest

open scoped BigOperators

end

end OAI
