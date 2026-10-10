import OAI.Computability.BinPacking.PCP.PreprocessingGuarantees

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingPaddingOffsets

open PreprocessingRegularTables
open scoped BigOperators

private theorem idxOf_map_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (a : A) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = a
    · subst x; simp
    · simp [List.idxOf_cons_ne, h, hf.ne h, ih]

theorem sigma_idxOf {A : Type*} [DecidableEq A] (sizes : A → Nat)
    (xs : List A) (a : A) (ha : a ∈ xs) (j : Fin (sizes a)) :
    (xs.sigma (fun x => List.finRange (sizes x))).idxOf ⟨a, j⟩ =
      ((xs.take (xs.idxOf a)).map sizes).sum + j.val := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.sigma_cons]
    by_cases h : x = a
    · subst x
      have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∈
          (List.finRange (sizes a)).map (Sigma.mk a) := by
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
      rw [List.idxOf_append_of_mem hm,
        idxOf_map_injective (Sigma.mk a) (fun x y h => by cases h; rfl),
        List.idxOf_finRange]
      simp
    · have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∉
          (List.finRange (sizes x)).map (Sigma.mk x) := by
        intro hm
        rcases List.mem_map.mp hm with ⟨k, _, hk⟩
        exact h (congrArg Sigma.fst hk)
      rw [List.idxOf_append_of_notMem hm, List.length_map, List.length_finRange,
        ih (List.mem_of_ne_of_mem (Ne.symm h) ha), List.idxOf_cons_ne xs h]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

def offset {n : Nat} (padding : Fin n → Nat) (k : Nat) : Nat :=
  (((List.finRange n).take k).map padding).sum

theorem sigma_length {A : Type*} (sizes : A → Nat) (xs : List A) :
    (xs.sigma (fun x => List.finRange (sizes x))).length = (xs.map sizes).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.sigma_cons, ih]

theorem paddingOrder_val {n : Nat} (padding : Fin n → Nat)
    (v : Fin n) (j : Fin (padding v)) :
    (PreprocessingRegularTables.paddingOrder padding ⟨v, j⟩).val =
      offset padding v.val + j.val := by
  change (paddingList padding).idxOf ⟨v, j⟩ = _
  have h := sigma_idxOf padding (List.finRange n) v (List.mem_finRange v) j
  simpa only [List.idxOf_finRange, paddingList, offset] using h

theorem vertexOrder_dummy_val (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (v : Fin t.vertices) (j : Fin (padding v)) :
    (vertexOrder t padding (Sum.inr ⟨v, j⟩)).val =
      t.darts + offset padding v.val + j.val := by
  rw [vertexOrder_dummy, paddingOrder_val]
  omega

@[simp] theorem offset_zero {n : Nat} (padding : Fin n → Nat) : offset padding 0 = 0 := by
  simp [offset]

theorem offset_all {n : Nat} (padding : Fin n → Nat) :
    offset padding n = ∑ v, padding v := by
  have ht : (List.finRange n).take n = List.finRange n := by simp
  unfold offset
  rw [ht, ← sigma_length padding (List.finRange n)]
  exact paddingList_length padding

end BinPackingGames.Foundations.PCP.PreprocessingPaddingOffsets

namespace BinPackingGames.Foundations.PCP.PreprocessingInternalRows

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

private theorem relation_ext {r s : GraphTables.RelationTable}
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

end BinPackingGames.Foundations.PCP.PreprocessingInternalRows

namespace BinPackingGames.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open BinPackingGames.Foundations.Complexity
open scoped BigOperators

def inputLength (t : GraphTables.Table) : Nat := (GraphTables.tableBits t).length

theorem cloudSize_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    cloudSize t v ≤ inputLength t :=
  (cloudSize_le_darts t v).trans (GraphTables.darts_le_tableBits_length t)

theorem cloudTotal_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    cloudSize t v + padding t v ≤ ExpanderFamily.growth * inputLength t := by
  rw [cloudSize_add_padding]
  exact (PreprocessingLevels.cloudPaddedSize_bounds _).2.trans
    (Nat.mul_le_mul_left _ (cloudSize_le_input t v))

theorem level_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    PreprocessingLevels.boundedLevel (cloudSize t v) ≤ inputLength t :=
  (PreprocessingLevels.boundedLevel_le_input _).trans (cloudSize_le_input t v)

theorem regularVertices_le_input (t : GraphTables.Table) :
    vertexCount t (padding t) ≤ ExpanderFamily.growth * inputLength t :=
  (vertexCount_le t).trans
    (Nat.mul_le_mul_left _ (GraphTables.darts_le_tableBits_length t))

theorem offset_le_sum {n : Nat} (p : Fin n → Nat) (k : Nat) :
    PreprocessingPaddingOffsets.offset p k ≤ ∑ v, p v := by
  have hfull : (List.finRange n).take n = List.finRange n := by simp
  have hsplit : PreprocessingPaddingOffsets.offset p k +
      (((List.finRange n).drop k).map p).sum =
      PreprocessingPaddingOffsets.offset p n := by
    simp only [PreprocessingPaddingOffsets.offset, hfull]
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  rw [PreprocessingPaddingOffsets.offset_all] at hsplit
  omega

theorem prefix_le_input (t : GraphTables.Table) (k : Nat) :
    PreprocessingPaddingOffsets.offset (padding t) k ≤
      ExpanderFamily.growth * inputLength t := by
  have hsum : (∑ v, padding t v) ≤ vertexCount t (padding t) := by
    unfold vertexCount
    omega
  exact (offset_le_sum (padding t) k).trans (hsum.trans (regularVertices_le_input t))

noncomputable def tablePolynomial (a b : Nat) : Polynomial Nat :=
  Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 2 +
    (Polynomial.C b * Polynomial.X) *
      (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 8192)

theorem tableBits_le_of_counts (t : GraphTables.Table) (a b L : Nat)
    (hv : t.vertices ≤ a * L) (he : t.darts ≤ b * L) :
    (GraphTables.tableBits t).length ≤ (tablePolynomial a b).eval L := by
  have hsum := Nat.add_le_add hv he
  have hprod := Nat.mul_le_mul he (Nat.add_le_add_right hsum 8192)
  have h := (GraphTables.tableBits_length_le t).trans
    (Nat.add_le_add (Nat.add_le_add_right hsum 2) hprod)
  simpa only [tablePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

noncomputable def regularPolynomial : Polynomial Nat :=
  tablePolynomial ExpanderFamily.growth (ExpanderFamily.growth * (internalDegree + 1))

theorem regularBits_le (H : BaseTable) (t : GraphTables.Table) :
    (PortTables.tableBits (regularize H t)).length ≤
      regularPolynomial.eval (inputLength t) := by
  have hv : (PortTables.graphTable (regularize H t)).vertices ≤
      ExpanderFamily.growth * inputLength t := regularVertices_le_input t
  have he : (PortTables.graphTable (regularize H t)).darts ≤
      (ExpanderFamily.growth * (internalDegree + 1)) * inputLength t := by
    change vertexCount t (padding t) * (internalDegree + 1) ≤ _
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * (internalDegree + 1) :=
        Nat.mul_le_mul_right _ hv
      _ = _ := by ac_rfl
  exact tableBits_le_of_counts (PortTables.graphTable (regularize H t)) _ _ _ hv he

noncomputable def rotorPolynomial (q : Nat) : Polynomial Nat :=
  (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X) *
    (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X + 1)

theorem cloudRotorBits_le (t : GraphTables.Table) (v : Fin t.vertices) {q : Nat}
    (table : ExpanderTables.Table (cloudSize t v + padding t v) q) :
    (encodeWords (ExpanderTableWords.rotationWords table)).length ≤
      (rotorPolynomial q).eval (inputLength t) := by
  have hd : (cloudSize t v + padding t v) * q ≤
      (ExpanderFamily.growth * q) * inputLength t := by
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * q :=
        Nat.mul_le_mul_right _ (cloudTotal_le_input t v)
      _ = _ := by ac_rfl
  have h := (ExpanderTableWords.encode_rotationWords_length_le table).trans
    (Nat.mul_le_mul hd (Nat.add_le_add_right hd 1))
  simpa only [rotorPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end BinPackingGames.Foundations.PCP.PreprocessingMachineBounds

end OAI
