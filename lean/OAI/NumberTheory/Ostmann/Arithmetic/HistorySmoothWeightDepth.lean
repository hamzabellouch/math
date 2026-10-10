import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRegular
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicCost

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicSlots
open HistoryOccurrenceVariables HistorySymbolicStep HistorySymbolicCost
variable {ι : Type*}

theorem logSize_eq_atomCount (e : Expr ι) : e.logSize = e.atomCount := by
  induction e with
  | atom i => rfl
  | fixed c => rfl
  | add a b ia ib | sub a b ia ib | mul a b ia ib | divide a b ia ib =>
    simp only [Expr.logSize,Expr.atomCount,ia,ib]

def StateDepth (d : ℕ) {a : State} (e : StateExpr a ι) : Prop :=
  e.plus.cancellationDepth ≤ d ∧ e.minus.cancellationDepth ≤ d ∧
    ∀ i, (e.small i).cancellationDepth = 0

theorem stateDepth_mono {d D : ℕ} (h : d ≤ D) {a : State} (e : StateExpr a ι)
    (he : StateDepth d e) : StateDepth D e := ⟨he.1.trans h,he.2.1.trans h,he.2.2⟩

theorem children_depth {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (d : ℕ)
    (he : StateDepth d e) (hc : ∀ i, (comp i).cancellationDepth = 0) :
    StateDepth (d+1) (leftState hs e comp) ∧ StateDepth (d+1) (rightState hs e comp) := by
  have hleft : ∀ i, (leftPart (splitSlots hs e) i).cancellationDepth = 0 := fun i => he.2.2 _
  have hright : ∀ i, (rightPart (splitSlots hs e) i).cancellationDepth = 0 := fun i => he.2.2 _
  have hlist {n : ℕ} (f : Fin n → Expr ι) (hf : ∀ i, (f i).cancellationDepth = 0) :
      ∀ z ∈ List.ofFn f, z.cancellationDepth = 0 := by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact hf i
  have hpivot := pivot_cancellationDepth_le a.frequency left.root.frequency right.root.frequency
    e.plus e.minus _ _ _ d he.1 he.2.1 (hlist comp hc) (hlist _ hleft) (hlist _ hright)
  exact ⟨⟨hpivot,he.1.trans (Nat.le_succ d),fun i =>
      append_forall (fun z => z.cancellationDepth = 0) comp _ hc hleft _⟩,
    ⟨hpivot,he.2.1.trans (Nat.le_succ d),fun i =>
      append_forall (fun z => z.cancellationDepth = 0) comp _ hc hright _⟩⟩

def TreeDepth (d : ℕ) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => StateDepth d e
  | _, .node _ _ _ _ _ left right, e =>
      StateDepth d e.1 ∧ TreeDepth d left e.2.1 ∧ TreeDepth d right e.2.2

theorem encode_depth {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) (d : ℕ) (he : StateDepth d e)
    (hc : ∀ i, (comp i).cancellationDepth = 0) :
    TreeDepth (d+l) h (encode V outside h hs e comp) := by
  induction h generalizing d with
  | leaf a => exact he
  | @node l a p u hp hm left right ihl ihr =>
    have hchild := children_depth hs e (fun i => comp (Sum.inl i)) d he (fun i => hc (Sum.inl i))
    refine ⟨stateDepth_mono (by omega) e he,?_,?_⟩
    · simpa only [encode,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ihl (History.supported_left hs) _ _ (d+1) hchild.1 (fun i => hc (Sum.inr (Sum.inl i)))
    · simpa only [encode,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ihr (History.supported_right hs) _ _ (d+1) hchild.2 (fun i => hc (Sum.inr (Sum.inr i)))

theorem symbolicHistory_depth {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) : TreeDepth l h (symbolicHistory h hs) := by
  have he := encode_depth h hs (rootExpr h) (compensationExpr h) 0
    ⟨le_rfl,le_rfl,fun _ => rfl⟩ (fun _ => rfl)
  simpa only [Nat.zero_add,symbolicHistory] using he

def TreeBudgetLe (K B : ℝ) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => e.plus.logBudget K ≤ B ∧ e.minus.logBudget K ≤ B
  | _, .node _ _ _ _ _ left right, e =>
      (e.1.plus.logBudget K ≤ B ∧ e.1.minus.logBudget K ≤ B) ∧
      TreeBudgetLe K B left e.2.1 ∧ TreeBudgetLe K B right e.2.2

theorem state_budget_le {K : ℝ} (hK : 1 ≤ K) {a : State} (e : StateExpr a ι)
    (B d : ℕ) (hcost : stateCost e ≤ B) (hdepth : StateDepth d e) :
    e.plus.logBudget K ≤ (B:ℝ)*K^d ∧ e.minus.logBudget K ≤ (B:ℝ)*K^d := by
  have hbound (z : Expr ι) (hz : z.atomCount ≤ B) (hd : z.cancellationDepth ≤ d) :
      z.logBudget K ≤ (B:ℝ)*K^d := by
    unfold Expr.logBudget
    rw [logSize_eq_atomCount]
    exact mul_le_mul (by exact_mod_cast hz) (pow_le_pow_right₀ hK hd)
      (pow_nonneg (zero_le_one.trans hK) _) (Nat.cast_nonneg B)
  constructor
  · apply hbound e.plus _ hdepth.1
    unfold stateCost at hcost
    omega
  · apply hbound e.minus _ hdepth.2.1
    unfold stateCost at hcost
    omega

theorem tree_budget_le {K : ℝ} (hK : 1 ≤ K) (B d : ℕ) {l : ℕ}
    (h : History l) (e : TreeExpr ι h) (hc : TreeCostLe B h e) (hd : TreeDepth d h e) :
    TreeBudgetLe K ((B:ℝ)*K^d) h e := by
  induction h with
  | leaf a => exact state_budget_le hK e B d hc hd
  | @node l a p u hp hm left right ihl ihr =>
    exact ⟨state_budget_le hK e.1 B d hc.1 hd.1,ihl _ hc.2.1 hd.2.1,ihr _ hc.2.2 hd.2.2⟩

theorem symbolicHistory_budget_le {K : ℝ} (hK : 1 ≤ K) {l : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h : History l) (hs : h.Supported V outside) :
    TreeBudgetLe K ((2^l*(2+h.root.small.length+2*h.internalOccurrences.length):ℕ)*K^l)
      h (symbolicHistory h hs) :=
  tree_budget_le hK _ l h _ (symbolicHistory_cost_le h hs) (symbolicHistory_depth h hs)

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
