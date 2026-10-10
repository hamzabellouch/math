import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicEncoding

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicCost
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicSlots
open HistoryOccurrenceVariables HistorySymbolicEncoding

variable {ι : Type*}

def slotCost {n : ℕ} (f : Fin n → Expr ι) : ℕ := ∑ i, (f i).atomCount

def stateCost {a : State} (e : StateExpr a ι) : ℕ :=
  e.plus.atomCount + e.minus.atomCount + slotCost e.small

theorem slotCost_reorder {xs ys : List SmallSlot} (h : xs.Perm ys)
    (f : Fin xs.length → Expr ι) : slotCost (reorder h f) = slotCost f :=
  (OccurrencePermutation.indexEquiv h).symm.sum_comp (fun i => (f i).atomCount)

theorem slotCost_append {xs ys : List SmallSlot}
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι) :
    slotCost (append f g) = slotCost f + slotCost g := by
  have he := (finCongr (show (xs++ys).length=xs.length+ys.length from List.length_append)).sum_comp
    (fun i => (Fin.append f g i).atomCount)
  refine he.trans ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right,slotCost]

theorem slotCost_parts {xs ys : List SmallSlot} (f : Fin (xs++ys).length → Expr ι) :
    slotCost (leftPart f) + slotCost (rightPart f) = slotCost f := by
  have he := (finCongr (show (xs++ys).length=xs.length+ys.length from List.length_append)).symm.sum_comp
    (fun i => (f i).atomCount)
  rw [Fin.sum_univ_add] at he
  exact he

theorem sum_atomCount_ofFn {n : ℕ} (f : Fin n → Expr ι) :
    ((List.ofFn f).map Expr.atomCount).sum = slotCost f := by
  rw [List.map_ofFn,List.sum_ofFn]
  rfl

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem pivotExpr_atomCount
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) :
    (pivotExpr hs e comp).atomCount = stateCost e + slotCost comp := by
  unfold pivotExpr
  rw [HistorySymbolicStep.pivot_atomCount]
  simp only [sum_atomCount_ofFn]
  have hparts := slotCost_parts (splitSlots hs e)
  have hsplit := slotCost_reorder (History.supported_small_split hs) e.small
  change slotCost (splitSlots hs e) = slotCost e.small at hsplit
  unfold stateCost
  omega

theorem child_cost_le
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) :
    stateCost (leftState hs e comp) ≤ 2*(stateCost e + slotCost comp) ∧
    stateCost (rightState hs e comp) ≤ 2*(stateCost e + slotCost comp) := by
  have hparts := slotCost_parts (splitSlots hs e)
  have hsplit := slotCost_reorder (History.supported_small_split hs) e.small
  change slotCost (splitSlots hs e) = slotCost e.small at hsplit
  have hpivot := pivotExpr_atomCount hs e comp
  simp only [stateCost,leftState,rightState,slotCost_reorder,slotCost_append]
  unfold stateCost at hpivot
  constructor <;> omega

def TreeCostLe (B : ℕ) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => stateCost e ≤ B
  | _, .node _ _ _ _ _ left right, e =>
      stateCost e.1 ≤ B ∧ TreeCostLe B left e.2.1 ∧ TreeCostLe B right e.2.2

theorem treeCostLe_mono {A B : ℕ} (hab : A ≤ B) {l : ℕ} (h : History l)
    (e : TreeExpr ι h) (he : TreeCostLe A h e) : TreeCostLe B h e := by
  induction h with
  | leaf a => exact he.trans hab
  | @node l a p u hp hm left right ihl ihr =>
    exact ⟨he.1.trans hab,ihl _ he.2.1,ihr _ he.2.2⟩

def internalCost {l : ℕ} (h : History l) (comp : InternalKey h → Expr ι) : ℕ :=
  ∑ i, (comp i).atomCount

theorem internalCost_node (a : State) (p : ℕ) (u hp hm : List SmallSlot)
    (left right : History l) (comp : InternalKey (.node a p u hp hm left right) → Expr ι) :
    internalCost (.node a p u hp hm left right) comp =
      slotCost (fun i => comp (Sum.inl i)) +
        internalCost left (fun i => comp (Sum.inr (Sum.inl i))) +
        internalCost right (fun i => comp (Sum.inr (Sum.inr i))) := by
  simp only [internalCost,InternalKey,Fintype.sum_sum_type,slotCost]
  omega

theorem encode_cost_le {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) :
    TreeCostLe (2^l*(stateCost e+2*internalCost h comp)) h
      (encode V outside h hs e comp) := by
  induction h with
  | leaf a =>
    simp [TreeCostLe,encode,internalCost,InternalKey,History.root]
  | @node l a p u hp hm left right ihl ihr =>
    simp only [History.root] at *
    have hchildren := child_cost_le hs e (fun i => comp (Sum.inl i))
    have htotal := internalCost_node a p u hp hm left right comp
    have hpow : 1 ≤ 2^l := Nat.one_le_pow l 2 (by omega)
    have hpow' : 2^(l+1) = 2^l*2 := pow_succ 2 l
    refine ⟨?_,?_,?_⟩
    · have hbase : stateCost e ≤ stateCost e+2*internalCost (.node a p u hp hm left right) comp := by omega
      exact hbase.trans (Nat.le_mul_of_pos_left _ (by positivity))
    · apply treeCostLe_mono _ left _ (ihl (History.supported_left hs) _ _)
      rw [hpow', Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      simp only [History.root] at *
      omega
    · apply treeCostLe_mono _ right _ (ihr (History.supported_right hs) _ _)
      rw [hpow', Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      simp only [History.root] at *
      omega

theorem symbolicHistory_cost_le {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) :
    TreeCostLe (2^l*(2+h.root.small.length+2*h.internalOccurrences.length)) h
      (symbolicHistory h hs) := by
  have he := encode_cost_le h hs (rootExpr h) (compensationExpr h)
  have hone : (1:ℕ)+1=2 := rfl
  simpa only [symbolicHistory,stateCost,rootExpr,compensationExpr,Expr.atomCount,slotCost,internalCost,hone,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,internalKey_card,smul_eq_mul,mul_one]
    using he

end Ostmann.Arithmetic.HistorySymbolicCost

end

end OAI
