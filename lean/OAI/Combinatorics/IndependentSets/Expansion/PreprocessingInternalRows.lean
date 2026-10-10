import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PreprocessingPaddingOffsets

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingInternalRows

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

def localStep (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    Fin (cloudSize t v + padding v) × Fin q :=
  ExpanderTables.lookup (tables v) (paddedCloudRank t padding v x, p)

def destination (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    PaddedCloud t padding v :=
  paddedCloudSelect t padding v (localStep t padding tables v x p).1

def rowIndex (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    Fin (vertexCount t padding * (q + 1)) :=
  PortTables.rowIndex (vertexCount t padding) (q + 1)
    (vertexOrder t padding x.val, portOrder q (.inl p))

def row (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1)) :=
  (PortTables.flatRows (ofCloudTables t padding tables))[rowIndex t padding v x p]

def equalityRelation : GraphTables.RelationTable :=
  GraphTables.relationOf (fun a b => decide (a = b))

@[simp] theorem equalityRelation_apply (a b : GraphTables.Label) :
    GraphTables.relationAt equalityRelation a b = decide (a = b) :=
  GraphTables.relationAt_relationOf _ a b

theorem cloud_rotation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (cloudGraphs t padding tables v).rot (x, p) =
      (destination t padding tables v x p, (localStep t padding tables v x p).2) := by
  have h := GraphTransport.reindex_rot (ExpanderTables.graph (tables v))
    (paddedCloudEquiv t padding v).symm (Equiv.refl _)
    (paddedCloudRank t padding v x) p
  simpa only [cloudGraphs, ExpanderTables.graph_rot, Equiv.refl_apply,
    paddedCloudRank, paddedCloudSelect, Equiv.symm_apply_apply, destination, localStep] using h

theorem source_rotation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (sourcePortGraph t padding tables).rot (x.val, .inl p) =
      ((destination t padding tables v x p).val,
        .inl (localStep t padding tables v x p).2) := by
  rcases x with ⟨x, hx⟩
  subst v
  exact congrArg
    (fun z : PaddedCloud t padding
        ((paddedGraph (GraphTables.semantics t) (fun v => Fin (padding v))).tail x) × Fin q =>
      (z.1.val, (Sum.inl z.2 : Fin q ⊕ Unit)))
    (cloud_rotation t padding tables _ ⟨x, rfl⟩ p)

theorem rotation_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    PortTables.rotation (ofCloudTables t padding tables)
        (vertexOrder t padding x.val, portOrder q (.inl p)) =
      (vertexOrder t padding (destination t padding tables v x p).val,
        portOrder q (.inl (localStep t padding tables v x p).2)) := by
  rw [rotation_ofCloudTables, source_rotation t padding tables v x p]

theorem reverseIndex_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    ((ofCloudTables t padding tables).reverseIndex[rowIndex t padding v x p]).val =
      (q + 1) * (vertexOrder t padding (destination t padding tables v x p).val).val +
        (localStep t padding tables v x p).2.val := by
  unfold rowIndex
  rw [← PortTables.rowIndex_rotation, rotation_internal t padding tables v x p,
    PortTables.rowIndex_val, portOrder_internal]
  dsimp only
  omega

theorem relation_ext {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

theorem relations_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (ofCloudTables t padding tables).relations[rowIndex t padding v x p] = equalityRelation := by
  apply relation_ext
  intro a b
  rw [equalityRelation_apply]
  exact accepts_internal t padding tables x.val p a b

@[simp] theorem row_tail (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).tail.val = (vertexOrder t padding x.val).val := by
  simp only [row, rowIndex, PortTables.flatRows, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta, Equiv.symm_apply_apply]

theorem row_reverse (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).reverseIndex.val =
      (q + 1) * (vertexOrder t padding (destination t padding tables v x p).val).val +
        (localStep t padding tables v x p).2.val := by
  simpa only [row, PortTables.flatRows, Vector.getElem_ofFn, Fin.getElem_fin] using
    reverseIndex_internal t padding tables v x p

@[simp] theorem row_relation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).relation = equalityRelation := by
  simpa only [row, PortTables.flatRows, Vector.getElem_ofFn, Fin.getElem_fin] using
    relations_internal t padding tables v x p

@[simp] theorem localStep_original (v : Fin t.vertices) (x : Cloud (GraphTables.semantics t) v)
    (p : Fin q) :
    localStep t padding tables v (paddedOld t padding v x) p =
      ExpanderTables.lookup (tables v) (Fin.castAdd (padding v) (cloudRank t v x), p) := rfl

@[simp] theorem localStep_dummy (v : Fin t.vertices) (j : Fin (padding v)) (p : Fin q) :
    localStep t padding tables v (paddedNew t padding v j) p =
      ExpanderTables.lookup (tables v) (Fin.natAdd (cloudSize t v) j, p) := rfl

@[simp] theorem row_tail_original (v : Fin t.vertices) (x : Cloud (GraphTables.semantics t) v)
    (p : Fin q) :
    (row t padding tables v (paddedOld t padding v x) p).tail.val = x.val.val := by
  rw [row_tail]
  rfl

@[simp] theorem row_tail_dummy (v : Fin t.vertices) (j : Fin (padding v)) (p : Fin q) :
    (row t padding tables v (paddedNew t padding v j) p).tail.val =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val := by
  rw [row_tail]
  exact PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v j

def selectedIndex (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) : Nat :=
  if hi : i.val < cloudSize t v then
    (cloudSelect t v ⟨i.val, hi⟩).val.val
  else t.darts + PreprocessingPaddingOffsets.offset padding v.val + (i.val - cloudSize t v)

theorem selectedIndex_eq (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) :
    (vertexOrder t padding (paddedCloudSelect t padding v i).val).val =
      selectedIndex t padding v i := by
  unfold selectedIndex
  split
  · rename_i hi
    have he : i = Fin.castAdd (padding v) (⟨i.val, hi⟩ : Fin (cloudSize t v)) := Fin.ext rfl
    refine (congrArg (fun j =>
      (vertexOrder t padding (paddedCloudSelect t padding v j).val).val) he).trans ?_
    rw [paddedCloudSelect_castAdd]
    rfl
  · rename_i hi
    have hj : i.val - cloudSize t v < padding v := by have h := i.isLt; omega
    have he : i = Fin.natAdd (cloudSize t v) (⟨i.val - cloudSize t v, hj⟩ : Fin (padding v)) := by
      apply Fin.ext
      dsimp only [Fin.val_natAdd]
      omega
    refine (congrArg (fun j =>
      (vertexOrder t padding (paddedCloudSelect t padding v j).val).val) he).trans ?_
    rw [paddedCloudSelect_natAdd]
    change (vertexOrder t padding
      (Sum.inr ⟨v, (⟨i.val - cloudSize t v, hj⟩ : Fin (padding v))⟩)).val = _
    exact PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v _

theorem selectedIndex_old (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v))
    (hi : i.val < cloudSize t v) :
    selectedIndex t padding v i = (cloudSelect t v ⟨i.val, hi⟩).val.val := by
  simp only [selectedIndex, dite_eq_left hi]

theorem selectedIndex_dummy (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v))
    (hi : cloudSize t v ≤ i.val) :
    selectedIndex t padding v i =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + (i.val - cloudSize t v) := by
  simp only [selectedIndex, dite_eq_right (Nat.not_lt_of_ge hi)]

theorem row_reverse_selectedIndex (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).reverseIndex.val =
      (q + 1) * selectedIndex t padding v (localStep t padding tables v x p).1 +
        (localStep t padding tables v x p).2.val := by
  rw [row_reverse]
  unfold destination
  rw [selectedIndex_eq]

theorem rowWords_eq (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    GraphTables.rowWords (row t padding tables v x p) =
      [(vertexOrder t padding x.val).val,
        (q + 1) * selectedIndex t padding v (localStep t padding tables v x p).1 +
          (localStep t padding tables v x p).2.val] ++
        GraphTables.relationWords equalityRelation := by
  unfold GraphTables.rowWords
  rw [row_tail, row_reverse_selectedIndex, row_relation]

end IndependentSetsGames.Foundations.PCP.PreprocessingInternalRows

end OAI
