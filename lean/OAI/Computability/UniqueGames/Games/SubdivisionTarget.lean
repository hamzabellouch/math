import OAI.Computability.UniqueGames.Games.ProductTarget
import OAI.Computability.UniqueGames.Machines.MachineFixedCopiesLemmas

namespace OAI

/-!
Concrete numbered, full-table output for the four-edge subdivision.
Original vertices keep their names. The new names are `n+e`, `n+Q+2e`,
and `n+Q+2e+1`, and each input occurrence emits four consecutive rows.
-/

namespace UniqueGamesTheorem.Explicit.SubdivisionTarget

open UniqueGamesTheorem.Foundations Target
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

end UniqueGamesTheorem.Explicit.SubdivisionTarget

end OAI
