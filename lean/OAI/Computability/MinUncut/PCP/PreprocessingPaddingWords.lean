import Mathlib
import OAI.Computability.MinUncut.PCP.PreprocessingInternalRows
import OAI.Computability.MinUncut.Machines.MachineDummyRows

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem ofFn_split {α : Type*} (h : n ≤ m) (f : Fin m → α) :
    List.ofFn f =
      List.ofFn (fun v : Fin n => f (v.castLE h)) ++
        List.ofFn (fun v : Fin (m - n) => f (PreprocessingPaddingTables.vertexEquiv h (.inr v))) := by
  calc
    List.ofFn f = List.ofFn
        (fun v : Fin (n + (m - n)) => f (Fin.cast (Nat.add_sub_of_le h) v)) :=
      List.ofFn_congr (Nat.add_sub_of_le h).symm f
    _ = _ := by rw [List.ofFn_add]; rfl

theorem flatten_ofFn_rowIndex {α : Type*} (f : Fin (n * d) → List α) :
    (List.ofFn f).flatten =
      (List.ofFn (fun v : Fin n =>
        (List.ofFn (fun p : Fin d => f (rowIndex n d (v, p)))).flatten)).flatten := by
  rw [List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val, Nat.mul_comm, Nat.add_comm]

def rowBits (table : Table n d) (v : Fin n) (p : Fin d) : List Bool :=
  encodeWord v.val ++ encodeWord (table.reverseIndex[rowIndex n d (v, p)]).val ++
    encodeWords (GraphTables.relationWords table.relations[rowIndex n d (v, p)])

def vertexBits (table : Table n d) (v : Fin n) : List Bool :=
  (List.ofFn (fun p : Fin d => rowBits table v p)).flatten

def rowsBits (table : Table n d) : List Bool :=
  encodeWords ((flatRows table).toList.flatMap GraphTables.rowWords)

theorem rowBits_flat (table : Table n d) (i : Fin (n * d)) :
    encodeWords (GraphTables.rowWords ((flatRows table)[i])) =
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2 := by
  simp only [flatRows, Vector.getElem_ofFn, Fin.getElem_fin,
    MachineTableRows.rowBits_eq, rowBits, Prod.eta, Equiv.apply_symm_apply]

theorem rowsBits_eq_vertices (table : Table n d) :
    rowsBits table = (List.ofFn (fun v : Fin n => vertexBits table v)).flatten := by
  have hflat : (flatRows table).toList =
      List.ofFn (fun i : Fin (n * d) => (flatRows table)[i]) := by
    simp only [flatRows, Vector.toList_ofFn, Vector.getElem_ofFn, Fin.getElem_fin]
  unfold rowsBits
  rw [hflat, encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun i : Fin (n * d) =>
    encodeWords (GraphTables.rowWords ((flatRows table)[i])))).flatten = _
  simp_rw [rowBits_flat]
  simpa only [Equiv.symm_apply_apply, vertexBits] using
    flatten_ofFn_rowIndex (fun i : Fin (n * d) =>
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2)

theorem rowBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h) (v.castLE h) p = rowBits table v p := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_old,
    PreprocessingPaddingTables.relations_pad_old]
  have he : (rowIndex m d ((rotation table (v, p)).1.castLE h,
      (rotation table (v, p)).2)).val = (table.reverseIndex[rowIndex n d (v, p)]).val := by
    rw [← rowIndex_rotation]
    rfl
  rw [he]
  rfl

theorem rowBits_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h)
        (PreprocessingPaddingTables.vertexEquiv h (.inr v)) p =
      MachineDummyRows.rowBits (n + v.val) (p.val + d * (n + v.val)) := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_new,
    PreprocessingPaddingTables.relations_pad_new]
  rfl

theorem dummy_rowsBits_eq_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn (fun p : Fin count => MachineDummyRows.rowBits v (e + p.val))).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext p
    congr 1
    omega

theorem paddingBits_eq_ofFn (d v e count : Nat) :
    MachinePaddingRows.paddingBits d v e count =
      (List.ofFn (fun k : Fin count =>
        MachineDummyRows.rowsBits (v + k.val) (e + k.val * d) d)).flatten := by
  induction count generalizing v e with
  | zero => rfl
  | succ count ih =>
    rw [MachinePaddingRows.paddingBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, Fin.val_succ, Nat.add_mul, Nat.one_mul]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext k
    congr 1 <;> omega

@[simp] theorem vertexBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) :
    vertexBits (PreprocessingPaddingTables.pad table h) (v.castLE h) = vertexBits table v := by
  simp only [vertexBits, rowBits_pad_old]

theorem vertexBits_pad_new (table : Table n d) (h : n ≤ m) (v : Fin (m - n)) :
    vertexBits (PreprocessingPaddingTables.pad table h)
        (PreprocessingPaddingTables.vertexEquiv h (.inr v)) =
      MachineDummyRows.rowsBits (n + v.val) (n * d + v.val * d) d := by
  unfold vertexBits
  simp_rw [rowBits_pad_new]
  rw [dummy_rowsBits_eq_ofFn]
  apply congrArg (fun f : Fin d → List Bool => (List.ofFn f).flatten)
  funext p
  congr 1
  ring

theorem rowsBits_pad (table : Table n d) (h : n ≤ m) :
    rowsBits (PreprocessingPaddingTables.pad table h) =
      rowsBits table ++ MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  rw [rowsBits_eq_vertices, ofFn_split h, List.flatten_append]
  simp_rw [vertexBits_pad_old, vertexBits_pad_new]
  rw [← rowsBits_eq_vertices, ← paddingBits_eq_ofFn]

theorem tableBits_pad (table : Table n d) (h : n ≤ m) :
    tableBits (PreprocessingPaddingTables.pad table h) =
      encodeWords [m, m * d] ++ rowsBits table ++
        MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  change encodeWords (PortTables.tableWords (PreprocessingPaddingTables.pad table h)) = _
  rw [tableWords_eq, encodeWords_append]
  change encodeWords [m, m * d] ++ rowsBits (PreprocessingPaddingTables.pad table h) = _
  rw [rowsBits_pad, List.append_assoc]

end MinUncutGames.Foundations.PCP.PreprocessingPaddingWords

end
section
namespace MinUncutGames.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

def actualRow (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1)) :=
  (PortTables.flatRows (ofCloudTables t padding tables))[
    PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)]

def vertexRows (x : Vertex t padding) :
    List (GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1))) :=
  List.ofFn (fun p : Fin q => actualRow t padding tables x (.inl p)) ++
    [actualRow t padding tables x (.inr ())]

def originalVertexRows (e : Fin t.darts) := vertexRows t padding tables (.inl e)
def dummyVertexRows (v : Fin t.vertices) (j : Fin (padding v)) :=
  vertexRows t padding tables (.inr ⟨v, j⟩)

def vertexBits (x : Vertex t padding) : List Bool :=
  encodeWords ((vertexRows t padding tables x).flatMap GraphTables.rowWords)

def originalVertexBits (e : Fin t.darts) : List Bool := vertexBits t padding tables (.inl e)
def dummyVertexBits (v : Fin t.vertices) (j : Fin (padding v)) : List Bool :=
  vertexBits t padding tables (.inr ⟨v, j⟩)

theorem actualRow_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    actualRow t padding tables x.val (.inl p) =
      PreprocessingInternalRows.row t padding tables v x p := rfl

theorem actualRow_eq (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    actualRow t padding tables x p =
      ⟨vertexOrder t padding x,
        (ofCloudTables t padding tables).reverseIndex[
          PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)],
        (ofCloudTables t padding tables).relations[
          PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)]⟩ := by
  simp only [actualRow, PortTables.flatRows, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta, Equiv.symm_apply_apply]

@[simp] theorem actualRow_tail (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    (actualRow t padding tables x p).tail.val = (vertexOrder t padding x).val := by
  rw [actualRow_eq]

@[simp] theorem inherited_original_reverse (e : Fin t.darts) :
    (actualRow t padding tables (.inl e) (.inr ())).reverseIndex.val =
      (q + 1) * t.rows[e].reverseIndex.val + q := by
  rw [actualRow_eq]
  change ((ofCloudTables t padding tables).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t padding (.inl e), portOrder q (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t padding (.inl (GraphTables.reverseAt t.rows e)), portOrder q (.inr ()))).val = _
  rw [PortTables.rowIndex_val, vertexOrder_original, portOrder_inherited]
  exact Nat.add_comm _ _

@[simp] theorem inherited_dummy_reverse (v : Fin t.vertices) (j : Fin (padding v)) :
    (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())).reverseIndex.val =
      (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q := by
  rw [actualRow_eq]
  change ((ofCloudTables t padding tables).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t padding (.inr ⟨v, j⟩), portOrder q (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t padding (.inr ⟨v, j⟩), portOrder q (.inr ()))).val = _
  rw [PortTables.rowIndex_val, PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    portOrder_inherited]
  exact Nat.add_comm _ _

theorem relation_ext {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

@[simp] theorem inherited_original_relation (e : Fin t.darts) :
    (actualRow t padding tables (.inl e) (.inr ())).relation = t.rows[e].relation := by
  rw [actualRow_eq]
  apply relation_ext
  intro a b
  exact accepts_original t padding tables e a b

@[simp] theorem inherited_dummy_relation (v : Fin t.vertices) (j : Fin (padding v)) :
    (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())).relation =
      MachineDummyRows.trueRelation := by
  rw [actualRow_eq]
  apply relation_ext
  intro a b
  have h := accepts_dummy t padding tables ⟨v, j⟩ a b
  simpa only [PortTables.accepts, MachineDummyRows.trueRelation,
    GraphTables.relationAt, Fin.getElem_fin, Vector.getElem_replicate] using h

theorem inherited_original_words (e : Fin t.darts) :
    GraphTables.rowWords (actualRow t padding tables (.inl e) (.inr ())) =
      [e.val, (q + 1) * t.rows[e].reverseIndex.val + q] ++
        GraphTables.relationWords t.rows[e].relation := by
  simp only [GraphTables.rowWords, actualRow_tail, vertexOrder_original,
    inherited_original_reverse, inherited_original_relation]

theorem inherited_dummy_words (v : Fin t.vertices) (j : Fin (padding v)) :
    GraphTables.rowWords (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())) =
      [t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val,
        (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q] ++
        GraphTables.relationWords MachineDummyRows.trueRelation := by
  simp only [GraphTables.rowWords, actualRow_tail,
    PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    inherited_dummy_reverse, inherited_dummy_relation]

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem actualRow_bits (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    encodeWords (GraphTables.rowWords (actualRow t padding tables x p)) =
      PreprocessingPaddingWords.rowBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) (portOrder q p) := by
  simpa only [actualRow, Equiv.symm_apply_apply] using
    PreprocessingPaddingWords.rowBits_flat (ofCloudTables t padding tables)
      (PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p))

theorem vertexBits_eq (x : Vertex t padding) :
    vertexBits t padding tables x =
      PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) := by
  unfold vertexBits vertexRows
  rw [List.flatMap_append, encodeWords_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun p : Fin q =>
    encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inl p))))).flatten ++
      encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inr ()))) = _
  simp_rw [actualRow_bits]
  unfold PreprocessingPaddingWords.vertexBits
  rw [List.ofFn_succ_last, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

theorem paddingOrder_ofFn :
    List.ofFn (paddingOrder padding).symm = paddingList padding := by
  calc
    List.ofFn (paddingOrder padding).symm =
        List.ofFn (fun i : Fin (paddingList padding).length =>
          (paddingOrder padding).symm (Fin.cast (paddingList_length padding) i)) :=
      List.ofFn_congr (paddingList_length padding).symm (paddingOrder padding).symm
    _ = paddingList padding := by
      change List.ofFn (fun i => (paddingList padding).get i) = _
      exact List.ofFn_get _


theorem vertexOrder_ofFn {α : Type*} (f : Vertex t padding → α) :
    List.ofFn (fun i : Fin (vertexCount t padding) => f ((vertexOrder t padding).symm i)) =
      List.ofFn (fun e : Fin t.darts => f (.inl e)) ++
        (paddingList padding).map (fun z => f (.inr z)) := by
  change List.ofFn (fun i : Fin (t.darts + ∑ v, padding v) =>
    f ((vertexOrder t padding).symm i)) = _
  rw [List.ofFn_add]
  have hold (e : Fin t.darts) :
      (vertexOrder t padding).symm (e.castLE (Nat.le_add_right t.darts (∑ v, padding v))) =
        Sum.inl e := (vertexOrder t padding).symm_apply_apply (Sum.inl e)
  have hnew (i : Fin (∑ v, padding v)) :
      (vertexOrder t padding).symm (i.natAdd t.darts) =
        Sum.inr ((paddingOrder padding).symm i) := by
    apply (vertexOrder t padding).injective
    erw [Equiv.apply_symm_apply]
    change i.natAdd t.darts = Fin.natAdd t.darts
      ((paddingOrder padding) ((paddingOrder padding).symm i))
    rw [Equiv.apply_symm_apply]
  apply congrArg₂ (· ++ ·)
  · exact congrArg List.ofFn (funext (fun i => congrArg f (hold i)))
  · calc
      List.ofFn (fun i : Fin (∑ v, padding v) =>
          f ((vertexOrder t padding).symm (i.natAdd t.darts))) =
          List.ofFn (fun i => f (.inr ((paddingOrder padding).symm i))) :=
        congrArg List.ofFn (funext (fun i => congrArg f (hnew i)))
      _ = (List.ofFn (paddingOrder padding).symm).map (fun z => f (.inr z)) :=
        (List.map_ofFn (f := (paddingOrder padding).symm) (g := fun z => f (.inr z))).symm
      _ = _ := by rw [paddingOrder_ofFn]


theorem paddingList_flatMap {α : Type*} (f : (Σ v : Fin t.vertices, Fin (padding v)) → List α) :
    (paddingList padding).flatMap f =
      (List.ofFn (fun v : Fin t.vertices =>
        (List.ofFn (fun j : Fin (padding v) => f ⟨v, j⟩)).flatten)).flatten := by
  simp only [paddingList, List.sigma, List.finRange, List.flatMap_def,
    List.map_flatten, List.flatten_flatten, List.map_ofFn, Function.comp_def]

theorem rowsBits_ofCloudTables :
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) =
      (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  rw [PreprocessingPaddingWords.rowsBits_eq_vertices]
  have hblocks :
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables) i) =
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        vertexBits t padding tables ((vertexOrder t padding).symm i)) := by
    apply congrArg List.ofFn
    funext i
    rw [vertexBits_eq, Equiv.apply_symm_apply]
  rw [hblocks, vertexOrder_ofFn, List.flatten_append]
  change (List.ofFn (originalVertexBits t padding tables)).flatten ++
      ((paddingList padding).map (fun z => dummyVertexBits t padding tables z.1 z.2)).flatten = _
  rw [← List.flatMap_def, paddingList_flatMap]

theorem tableBits_ofCloudTables :
    PortTables.tableBits (ofCloudTables t padding tables) =
      encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
        (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  change encodeWords (PortTables.tableWords (ofCloudTables t padding tables)) = _
  rw [PortTables.tableWords_eq, encodeWords_append]
  change encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) = _
  rw [rowsBits_ofCloudTables, List.append_assoc]

end MinUncutGames.Foundations.PCP.PreprocessingRegularWords

end

end OAI
