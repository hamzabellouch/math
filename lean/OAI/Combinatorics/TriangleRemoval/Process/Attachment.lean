import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph
import OAI.Combinatorics.TriangleRemoval.Process.RootSet

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma lookupGraph_triangle {n : ℕ} {G : Graph n} {T : Finset (Fin n)}
    (hT : T ∈ triangles G) : BirthGraph.IsTriangle (lookupGraph G) T := by
  have ht := mem_triangles.mp hT
  refine ⟨ht.1,?_⟩
  intro x hx y hy hne
  refine ⟨hne,ht.2 ?_⟩
  exact Finset.mem_powersetCard.mpr ⟨by
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy,
    Finset.card_pair hne⟩

namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

noncomputable def attachment (v : Fin F.vertexCount) : Finset (Fin n) :=
  if hv : F.rootCount ≤ v.val then
    (F.incoming (F.callIndex v hv) (F.callIndex_nonroot v hv)).1 else ∅

noncomputable def birthParent (v : Fin F.vertexCount) : Option (Fin F.vertexCount) :=
  if hv : F.rootCount ≤ v.val then
    let i := F.callIndex v hv
    let hi := F.callIndex_nonroot v hv
    if hp : F.parent i hi ≠ F.root then some (F.birthIndex (F.parent i hi) hp) else none
  else none

lemma vertexLabel_nonroot (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.vertexLabel v = F.newVertex (F.callIndex v hv) (F.callIndex_nonroot v hv) := by
  rw [vertexLabel,dite_eq_right (Nat.not_lt.mpr hv)]

lemma attachment_nonroot (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.attachment v = (F.incoming (F.callIndex v hv) (F.callIndex_nonroot v hv)).1 := dite_eq_left hv

lemma attachment_birth (i : Fin F.size) (hi : i ≠ F.root) :
    F.attachment (F.birthIndex i hi) = (F.incoming i hi).1 := by
  rw [F.attachment_nonroot _ (F.birthIndex_nonroot i hi)]
  simp only [F.callIndex_birthIndex]

lemma birthParent_nonroot (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.birthParent v =
      if hp : F.parent (F.callIndex v hv) (F.callIndex_nonroot v hv) ≠ F.root then
        some (F.birthIndex _ hp) else none := dite_eq_left hv

lemma birthParent_some (v p : Fin F.vertexCount) (hv : F.rootCount ≤ v.val)
    (hp : F.birthParent v = some p) :
    ∃ h : F.parent (F.callIndex v hv) (F.callIndex_nonroot v hv) ≠ F.root,
      p = F.birthIndex _ h := by
  rw [F.birthParent_nonroot v hv] at hp
  split_ifs at hp with hh
  exact ⟨hh,(Option.some.inj hp).symm⟩

lemma birthParent_none (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val)
    (hp : F.birthParent v = none) :
    F.parent (F.callIndex v hv) (F.callIndex_nonroot v hv) = F.root := by
  rw [F.birthParent_nonroot v hv] at hp
  split_ifs at hp with hh
  exact not_ne_iff.mp hh

lemma birthParent_eq (v w : Fin F.vertexCount) (hv : F.rootCount ≤ v.val)
    (hw : F.rootCount ≤ w.val) (hp : F.birthParent v = F.birthParent w) :
    F.parent (F.callIndex v hv) (F.callIndex_nonroot v hv) =
      F.parent (F.callIndex w hw) (F.callIndex_nonroot w hw) := by
  cases hh : F.birthParent w with
  | none =>
    exact (F.birthParent_none v hv (hp.trans hh)).trans (F.birthParent_none w hw hh).symm
  | some p =>
    obtain ⟨hv',hpv⟩ := F.birthParent_some v p hv (hp.trans hh)
    obtain ⟨hw',hpw⟩ := F.birthParent_some w p hw hh
    exact F.birthIndex_injective _ _ hv' hw' (hpv.symm.trans hpw)

lemma newTriangle (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    insert (F.vertexLabel v) (F.attachment v) =
      (F.incoming (F.callIndex v hv) (F.callIndex_nonroot v hv)).2 := by
  rw [F.vertexLabel_nonroot v hv,F.attachment_nonroot v hv]
  exact (F.newVertex_spec _ _).2.symm

lemma attachments_distinct (v w : Fin F.vertexCount) (hv : F.rootCount ≤ v.val)
    (hw : F.rootCount ≤ w.val) (hp : F.birthParent v = F.birthParent w)
    (ha : F.attachment v = F.attachment w) (hl : F.vertexLabel v = F.vertexLabel w) : v = w := by
  have hpa := F.birthParent_eq v w hv hw hp
  have he : F.incoming (F.callIndex v hv) (F.callIndex_nonroot v hv) =
      F.incoming (F.callIndex w hw) (F.callIndex_nonroot w hw) := by
    apply Prod.ext
    · simpa only [F.attachment_nonroot v hv,F.attachment_nonroot w hw] using ha
    · rw [← F.newTriangle v hv,← F.newTriangle w hw,ha,hl]
  have hi := F.incoming_unique _ _ (F.callIndex_nonroot v hv) (F.callIndex_nonroot w hw) hpa he
  have hvw : F.birthIndex (F.callIndex v hv) (F.callIndex_nonroot v hv) =
      F.birthIndex (F.callIndex w hw) (F.callIndex_nonroot w hw) := by
    congr 1
  simpa only [F.birthIndex_callIndex] using hvw

end RecordedCallForest
end SharpTerminalLeave

end

end OAI
