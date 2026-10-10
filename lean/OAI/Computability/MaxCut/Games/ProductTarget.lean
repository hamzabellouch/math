import Mathlib
import OAI.Computability.MaxCut.Machines.MachineSubdivisionRows
import OAI.Computability.MaxCut.Machines.MachineBinaryParsing

namespace OAI

/-!
Explicit numbered permutation-table outputs for bipartite graphs and products.
All numbering maps are supplied as actual equivalences; the product uses the
computable radix equivalence with division/remainder inverse, never an arbitrary
finite-type enumeration. The value bridge preserves every list occurrence.
-/

namespace MaxCutGames.Explicit.ProductTarget

open MaxCutGames.Foundations
open Target
open MachineOutputContract
open scoped BigOperators

variable {L R E : Type*} {q N M : ℕ}

/-- Full forward and inverse tables of an explicit finite permutation. -/
def fullTable (p : Equiv.Perm (Fin q)) : PermutationTable q where
  images := Vector.ofFn p
  inverseImages := Vector.ofFn p.symm
  leftInverse a := by simp
  rightInverse a := by simp

@[simp] theorem fullTable_images (p : Equiv.Perm (Fin q)) (a : Fin q) :
    (fullTable p).images[a] = p a := by simp [fullTable]

@[simp] theorem permutationEquiv_fullTable (p : Equiv.Perm (Fin q)) :
    permutationEquiv (fullTable p) = p := by
  ext a
  simp [permutationEquiv, fullTable]

/-- One explicitly addressed row, with a separately supplied complete table. -/
def row (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ≃ Fin N)
    (edges : Fin M ≃ E) (tables : E → PermutationTable q) (i : Fin M) :
    Constraint N q where
  source := vertices (Sum.inl (G.left (edges i)))
  target := vertices (Sum.inr (G.right (edges i)))
  permutation := tables (edges i)

def render (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ≃ Fin N)
    (edges : Fin M ≃ E) (tables : E → PermutationTable q) (hM : 0 < M) :
    Instance q where
  vertices := N
  constraints := List.ofFn (row G vertices edges tables)
  nonempty := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp only [List.length_ofFn, List.length_nil] at hlength
    omega

@[simp] theorem render_length (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M) :
    (render G vertices edges tables hM).constraints.length = M := by
  simp [render]

theorem render_get (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (i : Fin (render G vertices edges tables hM).constraints.length) :
    (render G vertices edges tables hM).constraints[i] =
      row G vertices edges tables ⟨i.val, by simpa using i.isLt⟩ := by
  change (List.ofFn (row G vertices edges tables))[i.val]'(by simpa using i.isLt) = _
  exact List.getElem_ofFn (by simpa using i.isLt)

def render_simpleBipartite (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M) :
    SimpleBipartite (render G vertices edges tables hM) where
  side v := Sum.elim (fun _ => false) (fun _ => true) (vertices.symm v)
  sourceSide i := by simp only [render_get, row, Equiv.symm_apply_apply, Sum.elim_inl]
  targetSide i := by simp only [render_get, row, Equiv.symm_apply_apply, Sum.elim_inr]
  endpoints_injective := by
    intro i j hij
    have hi : i.val < M := by simpa using i.isLt
    have hj : j.val < M := by simpa using j.isLt
    have hrows :
        ((row G vertices edges tables ⟨i.val, hi⟩).source,
          (row G vertices edges tables ⟨i.val, hi⟩).target) =
        ((row G vertices edges tables ⟨j.val, hj⟩).source,
          (row G vertices edges tables ⟨j.val, hj⟩).target) := by
      simpa only [render_get] using! hij
    have hedge : edges ⟨i.val, hi⟩ = edges ⟨j.val, hj⟩ := by
      apply G.simple
      apply Prod.ext
      · exact Sum.inl.inj (vertices.injective (congrArg Prod.fst hrows))
      · exact Sum.inr.inj (vertices.injective (congrArg Prod.snd hrows))
    exact Fin.ext (congrArg (fun k : Fin M => k.val) (edges.injective hedge))

section Value

variable [Fintype L] [Fintype R] [Fintype E]

omit [Fintype L] [Fintype R] in
/-- A full vertex labeling pulls back to two independently local labelings. -/
theorem render_count (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e)
    (labeling : Fin N → Fin q) :
    countSatisfied labeling (render G vertices edges tables hM).constraints =
      G.satisfiedCount (fun x => labeling (vertices (Sum.inl x)))
        (fun y => labeling (vertices (Sum.inr y))) := by
  classical
  have ht (e : E) (a : Fin q) : (tables e).images[a] = G.permutation e a :=
    congrArg (fun p : Equiv.Perm (Fin q) => p a) (htable e)
  change countSatisfied labeling (List.ofFn (row G vertices edges tables)) = _
  rw [Integration.GapSemantics.countSatisfied_ofFn]
  unfold BipartiteGame.satisfiedCount
  apply Fintype.sum_equiv edges
  intro i
  simp [row, Constraint.satisfied, ht]

def mergeLabelings (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) : Fin N → Fin q :=
  fun v => Sum.elim left right (vertices.symm v)

omit [Fintype L] [Fintype R] in
@[simp] theorem mergeLabelings_left (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) (x : L) :
    mergeLabelings vertices left right (vertices (Sum.inl x)) = left x := by
  simp [mergeLabelings]

omit [Fintype L] [Fintype R] in
@[simp] theorem mergeLabelings_right (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) (y : R) :
    mergeLabelings vertices left right (vertices (Sum.inr y)) = right y := by
  simp [mergeLabelings]

omit [Fintype L] [Fintype R] in
theorem render_count_merge (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e)
    (left : L → Fin q) (right : R → Fin q) :
    countSatisfied (mergeLabelings vertices left right)
      (render G vertices edges tables hM).constraints = G.satisfiedCount left right := by
  simpa only [mergeLabelings_left, mergeLabelings_right] using
    render_count G vertices edges tables hM htable (mergeLabelings vertices left right)

theorem render_maxSatisfied (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e) :
    Integration.InstanceValue.maxSatisfied (render G vertices edges tables hM) =
      G.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    erw [render_count G vertices edges tables hM htable]
    exact G.satisfiedCount_le_maxSatisfied _ _
  · unfold BipartiteGame.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [← render_count_merge G vertices edges tables hM htable]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied
      (render G vertices edges tables hM) (mergeLabelings vertices labeling.1 labeling.2)

theorem render_value (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e) :
    Integration.InstanceValue.value (render G vertices edges tables hM) = G.value := by
  unfold Integration.InstanceValue.value BipartiteGame.value
  rw [render_maxSatisfied G vertices edges tables hM htable, render_length]
  have hcard : M = Fintype.card E := by simpa using Fintype.card_congr edges
  rw [hcard]

end Value

/-- The product order is increasing radix address, with coordinate zero the
least significant digit. The inverse computes each digit by division/modulo. -/
def tuples (n t : ℕ) : List (Fin t → Fin n) :=
  (List.finRange (n ^ t)).map finFunctionFinEquiv.symm

@[simp] theorem tuples_length (n t : ℕ) : (tuples n t).length = n ^ t := by
  simp [tuples]

theorem tuples_mem {n t : ℕ} (f : Fin t → Fin n) : f ∈ tuples n t := by
  apply List.mem_map.mpr
  exact ⟨finFunctionFinEquiv f, List.mem_finRange _, Equiv.symm_apply_apply _ _⟩

theorem tuples_nodup (n t : ℕ) : (tuples n t).Nodup :=
  (List.nodup_finRange _).map finFunctionFinEquiv.symm.injective

@[simp] theorem tuples_get (n t : ℕ) (i : Fin (n ^ t)) :
    (tuples n t)[i.val]'(by simpa only [tuples_length] using i.isLt) =
      finFunctionFinEquiv.symm i := by
  simp [tuples]

theorem tuple_address (n t : ℕ) (f : Fin t → Fin n) :
    (finFunctionFinEquiv f : ℕ) = ∑ i : Fin t, (f i : ℕ) * n ^ (i : ℕ) :=
  finFunctionFinEquiv_apply f

/-- The explicit address and `ofDigits` share the same least-significant-first
coordinate order, with no restriction on the radix beyond the digit type. -/
theorem address_eq_ofDigits {n t : ℕ} (f : Fin t → Fin n) :
    (finFunctionFinEquiv f : ℕ) = Nat.ofDigits n (List.ofFn (fun i => (f i : ℕ))) := by
  have hmap :
      (List.ofFn (fun i => (f i : ℕ))).mapIdx (fun i a => a * n ^ i) =
        List.ofFn (fun i : Fin t => (f i : ℕ) * n ^ (i : ℕ)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [finFunctionFinEquiv_apply, Nat.ofDigits_eq_sum_mapIdx, hmap, List.sum_ofFn]

/-- A forward Horner controller reads the coordinate words in reverse order.
This is a word-order identity, separate from its machine execution theorem. -/
theorem address_eq_horner {n t : ℕ} (f : Fin t → Fin n) :
    (finFunctionFinEquiv f : ℕ) =
      (List.ofFn (fun i => (f i : ℕ))).reverse.foldl
        (fun acc digit => n * acc + digit) 0 := by
  rw [address_eq_ofDigits, Nat.ofDigits_eq_foldr, List.foldl_reverse]
  simp only [Nat.cast_id, Nat.add_comm]

end MaxCutGames.Explicit.ProductTarget

/-!
Concrete numbered, full-table output for the v2 four-edge subdivision.
Original vertices keep their names. The new names are `n+e`, `n+Q+2e`,
and `n+Q+2e+1`, and each input occurrence emits four consecutive rows.
-/

namespace MaxCutGames.Explicit.SubdivisionTarget

open MaxCutGames.Foundations Target
open MachineOutputContract
open scoped BigOperators

/-- Retain every original list occurrence as its own edge identifier. -/
def ofInstance {q : Nat} (H : Instance q) :
    OccurrenceGame (Fin H.vertices) (Fin H.constraints.length) (Fin q) where
  source e := H.constraints[e].source
  target e := H.constraints[e].target
  permutation e := permutationEquiv H.constraints[e].permutation

theorem ofInstance_count {q : Nat} (H : Instance q) (a : Fin H.vertices → Fin q) :
    (ofInstance H).satisfiedCount a = countSatisfied a H.constraints := by
  have h := Integration.GapSemantics.countSatisfied_ofFn a
    (fun i : Fin H.constraints.length => H.constraints[i.val])
  rw [List.ofFn_getElem] at h
  rw [h]
  simp only [OccurrenceGame.satisfiedCount, ofInstance, permutationEquiv,
    Equiv.coe_fn_mk, Constraint.satisfied, decide_eq_true_eq, Fin.getElem_fin]
  rfl

theorem ofInstance_maxSatisfied {q : Nat} (H : Instance q) :
    (ofInstance H).maxSatisfied = Integration.InstanceValue.maxSatisfied H := by
  classical
  unfold OccurrenceGame.maxSatisfied Integration.InstanceValue.maxSatisfied
  apply Finset.sup_congr
  · ext a
    simp only [Finset.mem_univ]
  · intro a _
    exact ofInstance_count H a

theorem ofInstance_value {q : Nat} (H : Instance q) :
    (ofInstance H).value = Integration.InstanceValue.value H := by
  unfold OccurrenceGame.value Integration.InstanceValue.value
  rw [ofInstance_maxSatisfied]
  simp

/-- Number `p_e` by `2e` and `r_e` by `2e+1`. -/
def numericRightEquiv (Q : Nat) : Fin Q × Bool ≃ Fin (Q * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin Q)) finTwoEquiv.symm).trans finProdFinEquiv

@[simp] theorem numericRightEquiv_false_val (Q : Nat) (e : Fin Q) :
    (numericRightEquiv Q (e, false)).val = 2 * e.val := by
  change 0 + 2 * e.val = 2 * e.val
  exact Nat.zero_add _

@[simp] theorem numericRightEquiv_true_val (Q : Nat) (e : Fin Q) :
    (numericRightEquiv Q (e, true)).val = 2 * e.val + 1 := by
  change 1 + 2 * e.val = 2 * e.val + 1
  exact Nat.add_comm _ _

/-- Original vertices, middle vertices, then interleaved `p_e,r_e`. -/
def numericVertexEquiv (n Q : Nat) :
    (Fin n ⊕ Fin Q) ⊕ (Fin Q × Bool) ≃ Fin (n + 3 * Q) :=
  ((Equiv.sumCongr
      (finSumFinEquiv : Fin n ⊕ Fin Q ≃ Fin (n + Q))
      (numericRightEquiv Q)).trans
    (finSumFinEquiv : Fin (n + Q) ⊕ Fin (Q * 2) ≃ Fin ((n + Q) + Q * 2))).trans
      (finCongr (by ring : (n + Q) + Q * 2 = n + 3 * Q))

@[simp] theorem numericVertexEquiv_original_val (n Q : Nat) (v : Fin n) :
    (numericVertexEquiv n Q (Sum.inl (Sum.inl v))).val = v.val := rfl

@[simp] theorem numericVertexEquiv_middle_val (n Q : Nat) (e : Fin Q) :
    (numericVertexEquiv n Q (Sum.inl (Sum.inr e))).val = n + e.val := rfl

@[simp] theorem numericVertexEquiv_p_val (n Q : Nat) (e : Fin Q) :
    (numericVertexEquiv n Q (Sum.inr (e, false))).val = n + Q + 2 * e.val := by
  change n + Q + (0 + 2 * e.val) = n + Q + 2 * e.val
  rw [Nat.zero_add]

@[simp] theorem numericVertexEquiv_r_val (n Q : Nat) (e : Fin Q) :
    (numericVertexEquiv n Q (Sum.inr (e, true))).val = n + Q + 2 * e.val + 1 := by
  change n + Q + (1 + 2 * e.val) = n + Q + 2 * e.val + 1
  omega

/-- The occurrence `e` occupies output indices `4e,4e+1,4e+2,4e+3`. -/
def numericEdgeEquiv (Q : Nat) : Fin (4 * Q) ≃ Fin Q × Fin 4 :=
  (finCongr (Nat.mul_comm 4 Q)).trans finProdFinEquiv.symm

@[simp] theorem numericEdgeEquiv_symm_val (Q : Nat) (e : Fin Q) (i : Fin 4) :
    ((numericEdgeEquiv Q).symm (e, i)).val = 4 * e.val + i.val := by
  change i.val + 4 * e.val = 4 * e.val + i.val
  exact Nat.add_comm _ _

def tables {q : Nat} (H : Instance q) (ei : Fin H.constraints.length × Fin 4) :
    PermutationTable q :=
  if ei.2 = 3 then MachineSubdivisionRows.inverseTable H.constraints[ei.1].permutation
  else MachineSubdivisionRows.identityTable q

theorem tables_correspond {q : Nat} (H : Instance q)
    (ei : Fin H.constraints.length × Fin 4) :
    permutationEquiv (tables H ei) = (Subdivision.game (ofInstance H)).permutation ei := by
  ext a
  by_cases hi : ei.2 = 3 <;>
    simp [tables, permutationEquiv, Subdivision.game, Subdivision.permutation, ofInstance,
      MachineSubdivisionRows.inverseTable, MachineSubdivisionRows.identityTable, hi]

/-- The five physical fields consumed by the checked row-emission phase. -/
def vertexFields {q : Nat} (H : Instance q) (e : Fin H.constraints.length) :
    Fin 5 → Fin (H.vertices + 3 * H.constraints.length) :=
  ![numericVertexEquiv _ _ (Sum.inl (Sum.inl H.constraints[e].source)),
    numericVertexEquiv _ _ (Sum.inr (e, false)),
    numericVertexEquiv _ _ (Sum.inl (Sum.inr e)),
    numericVertexEquiv _ _ (Sum.inr (e, true)),
    numericVertexEquiv _ _ (Sum.inl (Sum.inl H.constraints[e].target))]

theorem vertexFields_val {q : Nat} (H : Instance q) (e : Fin H.constraints.length)
    (j : Fin 5) :
    (vertexFields H e j).val = MachineSubdivisionRows.subdivisionVertexWords
      H.vertices H.constraints.length H.constraints[e].source.val
        H.constraints[e].target.val e.val j := by
  fin_cases j <;> simp [vertexFields, MachineSubdivisionRows.subdivisionVertexWords]

/-- Four consecutive semantic rows are exactly the four full-table rows emitted
by the machine phase, including the inverse table in the final row. -/
theorem rows_eq {q : Nat} (H : Instance q) (e : Fin H.constraints.length) :
    List.ofFn (fun i : Fin 4 => ProductTarget.row (Subdivision.game (ofInstance H))
      (numericVertexEquiv H.vertices H.constraints.length)
      (numericEdgeEquiv H.constraints.length) (tables H)
      ((numericEdgeEquiv H.constraints.length).symm (e, i))) =
    MachineSubdivisionRows.rows (vertexFields H e) H.constraints[e].permutation := by
  simp [List.ofFn_succ, ProductTarget.row, Subdivision.game, Subdivision.left,
    Subdivision.right, ofInstance, tables, vertexFields, MachineSubdivisionRows.rows]

theorem tables_translation {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (hH : Integration.TranslationTarget.IsTranslationInstance coordinates H)
    (ei : Fin H.constraints.length × Fin 4) :
    ∃ shift : Integration.BinaryLinear.Vector s, ∀ a : Fin q,
      coordinates ((tables H ei).images[a]) = coordinates a + shift := by
  by_cases hi : ei.2 = 3
  · obtain ⟨shift, hs⟩ := hH H.constraints[ei.1] (List.getElem_mem ei.1.isLt)
    refine ⟨shift, ?_⟩
    intro a
    simp only [tables, hi, ite_eq_left, MachineSubdivisionRows.inverseTable]
    have h := hs (H.constraints[ei.1].permutation.inverseImages[a])
    rw [H.constraints[ei.1].permutation.rightInverse] at h
    have hc := congrArg (fun x => x + shift) h
    simpa only [add_assoc, ZModModule.add_self, add_zero] using hc.symm
  · refine ⟨0, ?_⟩
    intro a
    simp [tables, hi, MachineSubdivisionRows.identityTable]

/-- A deterministic full-table occurrence list with exactly four rows per input row. -/
def subdivide {q : Nat} (H : Instance q) : Instance q :=
  ProductTarget.render (Subdivision.game (ofInstance H))
    (numericVertexEquiv H.vertices H.constraints.length)
    (numericEdgeEquiv H.constraints.length) (tables H)
    (by have h := H.constraintCount_positive; omega)

@[simp] theorem subdivide_vertices {q : Nat} (H : Instance q) :
    (subdivide H).vertices = H.vertices + 3 * H.constraints.length := rfl

@[simp] theorem subdivide_length {q : Nat} (H : Instance q) :
    (subdivide H).constraints.length = 4 * H.constraints.length := by
  apply ProductTarget.render_length

theorem subdivide_translation {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (hH : Integration.TranslationTarget.IsTranslationInstance coordinates H) :
    Integration.TranslationTarget.IsTranslationInstance coordinates (subdivide H) := by
  intro c hc
  change c ∈ List.ofFn _ at hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact tables_translation coordinates H hH (numericEdgeEquiv H.constraints.length i)

def simpleBipartite {q : Nat} (H : Instance q) : SimpleBipartite (subdivide H) :=
  ProductTarget.render_simpleBipartite _ _ _ _ _

theorem numeric_side (n Q : Nat) (v : Fin (n + 3 * Q)) :
    Sum.elim (fun _ => false) (fun _ => true) ((numericVertexEquiv n Q).symm v) =
      decide (n + Q ≤ v.val) := by
  obtain ⟨x, rfl⟩ := (numericVertexEquiv n Q).surjective v
  rcases x with (v | e) | ⟨e, b⟩
  · simp only [Equiv.symm_apply_apply, Sum.elim_inl, numericVertexEquiv_original_val]
    have h : ¬ n + Q ≤ v.val := by omega
    simp [h]
  · simp only [Equiv.symm_apply_apply, Sum.elim_inl, numericVertexEquiv_middle_val]
    have h : ¬ n + Q ≤ n + e.val := by omega
    simp [h]
  · cases b
    · simp only [Equiv.symm_apply_apply, Sum.elim_inr, numericVertexEquiv_p_val]
      have h : n + Q ≤ n + Q + 2 * e.val := by omega
      simp [h]
    · simp only [Equiv.symm_apply_apply, Sum.elim_inr, numericVertexEquiv_r_val]
      have h : n + Q ≤ n + Q + 2 * e.val + 1 := by omega
      simp [h]

/-- The concrete left side is precisely the first `n+Q` numeric names. -/
theorem simpleBipartite_side {q : Nat} (H : Instance q) (v : Fin (subdivide H).vertices) :
    (simpleBipartite H).side v = decide (H.vertices + H.constraints.length ≤ v.val) :=
  numeric_side H.vertices H.constraints.length v

/-- Satisfaction correspondence for every labeling of the actual numbered output. -/
theorem subdivide_count {q : Nat} (H : Instance q)
    (a : Fin (H.vertices + 3 * H.constraints.length) → Fin q) :
    countSatisfied a (subdivide H).constraints =
      (Subdivision.game (ofInstance H)).satisfiedCount
        (fun l => a (numericVertexEquiv H.vertices H.constraints.length (Sum.inl l)))
        (fun r => a (numericVertexEquiv H.vertices H.constraints.length (Sum.inr r))) :=
  ProductTarget.render_count _ _ _ _ _ (tables_correspond H) a

/-- The serialized output has exactly the abstract subdivision value. -/
theorem subdivide_value {q : Nat} (H : Instance q) :
    Integration.InstanceValue.value (subdivide H) =
      (Subdivision.game (ofInstance H)).value :=
  ProductTarget.render_value _ _ _ _ _ (tables_correspond H)

/-- Exact equation (bipartization-value) for the concrete list/table format. -/
theorem value_eq {q : Nat} (H : Instance q) (hq : 0 < q) :
    Integration.InstanceValue.value (subdivide H) =
      1 - (1 - Integration.InstanceValue.value H) / 4 := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [subdivide_value, Subdivision.value_eq, ofInstance_value]

end MaxCutGames.Explicit.SubdivisionTarget

end OAI
