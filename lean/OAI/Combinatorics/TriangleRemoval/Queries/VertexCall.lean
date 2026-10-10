import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth2
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraph
import OAI.Combinatorics.TriangleRemoval.Process.Parent
import OAI.Combinatorics.TriangleRemoval.Process.PathSuffix
import OAI.Combinatorics.TriangleRemoval.Process.SuffixProjection
import OAI.Combinatorics.TriangleRemoval.Queries.Address

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

def vertexCall (v : Fin F.vertexCount) : Fin F.size :=
  if hv : F.rootCount ≤ v.val then F.callIndex v hv else F.root

lemma vertexCall_nonroot (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.vertexCall v = F.callIndex v hv := dite_eq_left hv

lemma vertexCall_root (v : Fin F.vertexCount) (hv : v.val < F.rootCount) :
    F.vertexCall v = F.root := dite_eq_right (Nat.not_le.mpr hv)

lemma birthParent_vertexCall (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    (F.birthParent v).elim F.root F.vertexCall =
      F.parent (F.callIndex v hv) (F.callIndex_nonroot v hv) := by
  rw [F.birthParent_nonroot v hv]
  split_ifs with hp
  · simp only [Option.elim_some,vertexCall,dite_eq_left (F.birthIndex_nonroot _ hp),F.callIndex_birthIndex]
  · simpa only [Option.elim_none] using (not_ne_iff.mp hp).symm

lemma vertexCall_address (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    (F.call (F.vertexCall v)).address =
      (F.attachment v,insert (F.vertexLabel v) (F.attachment v)) ::
        (F.call ((F.birthParent v).elim F.root F.vertexCall)).address := by
  rw [F.vertexCall_nonroot v hv,F.birthParent_vertexCall v hv,
    F.newTriangle v hv,F.attachment_nonroot v hv]
  exact congrArg QueryCall.address (F.incoming_spec _ _).2

lemma vertexCall_address_empty_root (hc : c.address = [])
    (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    (F.call (F.vertexCall v)).address =
      (F.attachment v,insert (F.vertexLabel v) (F.attachment v)) ::
        (F.birthParent v).elim [] (fun p => (F.call (F.vertexCall p)).address) := by
  rw [F.vertexCall_address v hv]
  cases F.birthParent v <;> simp only [Option.elim_none,Option.elim_some,F.root_eq,hc]

lemma decoded_path_address (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)
    (hc : c.address = []) (a b : Fin F.vertexCount)
    (hR : F.rootCount ≤ F.vertexCount)
    (hi : Set.InjOn F.vertexLabel ((F.toTriangleGrowth hM hG).pathUnion a b))
    (i : Fin ((F.toTriangleGrowth hM hG).pathSuffix a b F.rootCount).card) :
    let A := F.toTriangleGrowth hM hG
    (A.pathForest a b).address
      (indexedTriangleKey (A.pathBirthIndex a b hR) (A.pathAttachments a b hR)
        (A.pathAssignment a b hi)) i =
      (F.call (F.vertexCall ((A.pathSuffix a b F.rootCount).orderEmbOfFin rfl i))).address := by
  dsimp only
  let A := F.toTriangleGrowth hM hG
  apply PathForest.address_unique
  intro j
  rw [A.indexedTriangleKey_actual a b hR hi j]
  have hv : F.rootCount ≤ ((A.pathSuffix a b F.rootCount).orderEmbOfFin rfl j).val :=
    ((A.mem_pathSuffix a b _ F.rootCount).mp
      ((A.pathSuffix a b F.rootCount).orderEmbOfFin_mem rfl j)).2
  rw [F.vertexCall_address_empty_root hc _ hv]
  congr 1
  cases hp : (A.pathForest a b).parent j with
  | none =>
    have he := (A.pathForest_parent_none a b j).mp hp
    change F.birthParent _ = none at he
    rw [he]
    rfl
  | some k =>
    have he := (A.pathForest_parent_some a b j k).mp hp
    change F.birthParent _ = some _ at he
    rw [he]
    rfl

lemma decoded_mark_address (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)
    (hc : c.address = []) (a b : Fin F.vertexCount)
    (hR : F.rootCount ≤ F.vertexCount)
    (hi : Set.InjOn F.vertexLabel ((F.toTriangleGrowth hM hG).pathUnion a b))
    (x : Fin F.vertexCount) (hx : x ∈ (F.toTriangleGrowth hM hG).pathUnion a b) :
    let A := F.toTriangleGrowth hM hG
    (suffixProjection (A.path_card_split a b hR) (A.pathIndex a b x hx)).elim []
      ((A.pathForest a b).address
        (indexedTriangleKey (A.pathBirthIndex a b hR) (A.pathAttachments a b hR)
          (A.pathAssignment a b hi))) = (F.call (F.vertexCall x)).address := by
  dsimp only
  let A := F.toTriangleGrowth hM hG
  rw [A.path_mark_projection a b hR x hx,PathForest.restrictMark]
  split_ifs with hn
  · simp only [Option.elim_some]
    rw [F.decoded_path_address hM hG hc a b hR hi]
    rw [PathForest.embed_index]
  · have hv : x.val < F.rootCount := by
      by_contra h
      exact hn ((A.mem_pathSuffix a b x F.rootCount).mpr ⟨hx,by omega⟩)
    rw [F.vertexCall_root x hv,F.root_eq,hc]
    rfl

end SharpTerminalLeave.RecordedCallForest

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
