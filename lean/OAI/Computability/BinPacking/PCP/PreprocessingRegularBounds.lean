import OAI.Computability.BinPacking.PCP.PreprocessingMachineBounds

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingRegularWords

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

private theorem relation_ext {r s : GraphTables.RelationTable}
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

private theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
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
  let order : Vertex t padding ≃ Fin (t.darts + ∑ v, padding v) := vertexOrder t padding
  change List.ofFn (fun i : Fin (t.darts + ∑ v, padding v) =>
    f (order.symm i)) = _
  rw [List.ofFn_add]
  have hold (e : Fin t.darts) :
      order.symm (e.castLE (Nat.le_add_right t.darts (∑ v, padding v))) =
        Sum.inl e := order.symm_apply_apply (Sum.inl e)
  have hnew (i : Fin (∑ v, padding v)) :
      order.symm (i.natAdd t.darts) =
        Sum.inr ((paddingOrder padding).symm i) := by
    apply order.injective
    rw [Equiv.apply_symm_apply]
    change i.natAdd t.darts = Fin.natAdd t.darts
      ((paddingOrder padding) ((paddingOrder padding).symm i))
    rw [Equiv.apply_symm_apply]
  simp_rw [hold, hnew]
  congr 1
  calc
    List.ofFn (fun i => f (.inr ((paddingOrder padding).symm i))) =
        (List.ofFn (paddingOrder padding).symm).map (fun z => f (.inr z)) :=
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

end BinPackingGames.Foundations.PCP.PreprocessingRegularWords

namespace BinPackingGames.Foundations.PCP.PreprocessingRegularLoopWords

def blocksPrefix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).take k).flatten

def blocksSuffix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).drop k).flatten

@[simp] theorem blocksPrefix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f 0 = [] := by
  simp only [blocksPrefix, List.take_zero, List.flatten_nil]

@[simp] theorem blocksPrefix_all {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f n = (List.ofFn f).flatten := by
  have h : (List.ofFn f).take n = List.ofFn f := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn f))
  exact congrArg List.flatten h

theorem blocksPrefix_succ {n : Nat} (f : Fin n → List Bool) (k : Nat) (h : k < n) :
    blocksPrefix f (k + 1) = blocksPrefix f k ++ f ⟨k, h⟩ := by
  unfold blocksPrefix
  rw [List.take_succ_eq_append_getElem
    (show k < (List.ofFn f).length by simpa only [List.length_ofFn] using h)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.getElem_ofFn]

@[simp] theorem blocksSuffix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f 0 = (List.ofFn f).flatten := by
  simp only [blocksSuffix, List.drop_zero]

@[simp] theorem blocksSuffix_all {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f n = [] := by
  have h : (List.ofFn f).drop n = [] := by
    simpa only [List.length_ofFn] using (List.drop_length (l := List.ofFn f))
  exact congrArg List.flatten h

theorem blocksSuffix_succ {n : Nat} (f : Fin n → List Bool) (k : Nat) (h : k < n) :
    blocksSuffix f k = f ⟨k, h⟩ ++ blocksSuffix f (k + 1) := by
  unfold blocksSuffix
  rw [List.drop_eq_getElem_cons
    (show k < (List.ofFn f).length by simpa only [List.length_ofFn] using h)]
  simp only [List.flatten_cons, List.getElem_ofFn]

theorem blocksPrefix_append_suffix {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    blocksPrefix f k ++ blocksSuffix f k = (List.ofFn f).flatten := by
  unfold blocksPrefix blocksSuffix
  rw [← List.flatten_append, List.take_append_drop]

end BinPackingGames.Foundations.PCP.PreprocessingRegularLoopWords

namespace BinPackingGames.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open BinPackingGames.Foundations.Complexity
open scoped BigOperators

theorem offset_succ {n : Nat} (p : Fin n → Nat) (k : Nat) (h : k < n) :
    PreprocessingPaddingOffsets.offset p (k + 1) =
      PreprocessingPaddingOffsets.offset p k + p ⟨k, h⟩ := by
  unfold PreprocessingPaddingOffsets.offset
  rw [List.take_succ_eq_append_getElem (show k < (List.finRange n).length by simpa using h)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.finRange, List.getElem_ofFn]

theorem blocksPrefix_length_le {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    (blocksPrefix f k).length ≤ (List.ofFn f).flatten.length := by
  have h := congrArg List.length (blocksPrefix_append_suffix f k)
  simp only [List.length_append] at h
  omega

def header (t : GraphTables.Table) (p : Fin t.vertices → Nat) (q : Nat) : List Bool :=
  encodeWords [vertexCount t p, vertexCount t p * (q + 1)]

def ownerBits (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) : List Bool :=
  (List.ofFn (dummyVertexBits t p tables v)).flatten

def originalPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ blocksPrefix (originalVertexBits t p tables) k

def ownerPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ (List.ofFn (originalVertexBits t p tables)).flatten ++
    blocksPrefix (ownerBits t p tables) k

def dummyPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) (k : Nat) : List Bool :=
  ownerPrefix t p tables v.val ++ blocksPrefix (dummyVertexBits t p tables v) k

variable (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)

theorem originalPrefix_length_le (k : Nat) :
    (originalPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (originalVertexBits t p tables) k
  rw [tableBits_ofCloudTables]
  simp only [originalPrefix, header, List.length_append]
  omega

theorem ownerPrefix_length_le (k : Nat) :
    (ownerPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (ownerBits t p tables) k
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  rw [tableBits_ofCloudTables]
  simp only [ownerPrefix, header, List.length_append] at *
  simp only [he] at *
  omega

theorem dummyPrefix_length_le (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t p tables v k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have hi := blocksPrefix_length_le (dummyVertexBits t p tables v) k
  have ho := blocksPrefix_length_le (ownerBits t p tables) (v.val + 1)
  rw [blocksPrefix_succ _ _ v.isLt] at ho
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  simp only [Fin.eta] at ho
  rw [tableBits_ofCloudTables]
  simp only [dummyPrefix, ownerPrefix, header, ownerBits, List.length_append] at *
  simp only [he] at *
  omega

theorem regular_originalPrefix_le (H : BaseTable) (k : Nat) :
    (originalPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (originalPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_ownerPrefix_le (H : BaseTable) (k : Nat) :
    (ownerPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (ownerPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_dummyPrefix_le (H : BaseTable) (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t (padding t) (familyCloudTable H t) v k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (dummyPrefix_length_le t (padding t) (familyCloudTable H t) v k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem visits_le_input :
    t.darts + t.vertices + (∑ v, padding t v) + 1 ≤
      (ExpanderFamily.growth + 1) * PreprocessingMachineBounds.inputLength t + 1 := by
  have hv := PreprocessingMachineBounds.regularVertices_le_input t
  have hn := GraphTables.vertices_le_tableBits_length t
  change t.vertices ≤ PreprocessingMachineBounds.inputLength t at hn
  unfold vertexCount at hv
  rw [Nat.add_mul, one_mul]
  omega

theorem sum_body_costs_le (old : Fin t.darts → Nat) (owners : Fin t.vertices → Nat)
    (dummy : ∀ v : Fin t.vertices, Fin (padding t v) → Nat) (setup cap : Nat)
    (hs : setup ≤ cap) (ho : ∀ e, old e ≤ cap) (hv : ∀ v, owners v ≤ cap)
    (hd : ∀ v j, dummy v j ≤ cap) :
    setup + (∑ e, old e) + (∑ v, owners v) + (∑ v, ∑ j, dummy v j) ≤
      ((ExpanderFamily.growth + 1) * PreprocessingMachineBounds.inputLength t + 1) * cap := by
  have hOld : (∑ e, old e) ≤ t.darts * cap := by
    simpa using Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => ho e)
  have hOwners : (∑ v, owners v) ≤ t.vertices * cap := by
    simpa using Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hv v)
  have hDummy : (∑ v, ∑ j, dummy v j) ≤ (∑ v, padding t v) * cap := by
    calc
      _ ≤ ∑ v, padding t v * cap := by
        apply Finset.sum_le_sum
        intro v _
        simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hd v j)
      _ = _ := (Finset.sum_mul ..).symm
  calc
    _ ≤ (t.darts + t.vertices + (∑ v, padding t v) + 1) * cap := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, one_mul]
      omega
    _ ≤ _ := Nat.mul_le_mul_right cap (visits_le_input t)

end BinPackingGames.Foundations.PCP.PreprocessingRegularBounds

end OAI
