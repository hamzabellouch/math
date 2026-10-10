import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightTreeDerivBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicCost
variable {ι : Type*}

def TreeRelativeControl (x : ι → ℝ) (K : ℝ) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => e.plus.RelativeControl x K ∧ e.minus.RelativeControl x K
  | _, .node _ _ _ _ _ left right, e =>
      (e.1.plus.RelativeControl x K ∧ e.1.minus.RelativeControl x K) ∧
      TreeRelativeControl x K left e.2.1 ∧ TreeRelativeControl x K right e.2.2

theorem treeRelativeControl_root (x : ι → ℝ) (K : ℝ) {l : ℕ} (h : History l)
    (e : TreeExpr ι h) (he : TreeRelativeControl x K h e) :
    (treeRoot h e).plus.RelativeControl x K ∧ (treeRoot h e).minus.RelativeControl x K := by
  cases h with
  | leaf a => exact he
  | node a p u hp hm left right => exact he.1

theorem treeBudgetLe_root (K B : ℝ) {l : ℕ} (h : History l)
    (e : TreeExpr ι h) (he : TreeBudgetLe K B h e) :
    (treeRoot h e).plus.logBudget K ≤ B ∧ (treeRoot h e).minus.logBudget K ≤ B := by
  cases h with
  | leaf a => exact he
  | node a p u hp hm left right => exact he.1

theorem StateSmallAtoms.length_le_cost {a : State} (e : StateExpr a ι) (he : StateSmallAtoms e) :
    a.small.length ≤ stateCost e := by
  have hslot : slotCost e.small = a.small.length := by
    unfold slotCost
    have hcount : ∀ i, (e.small i).atomCount = 1 := by
      intro i; obtain ⟨j,hj⟩ := he i; rw [hj]; rfl
    simp only [hcount,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  unfold stateCost
  omega

theorem treeDerivativeBudget_of_cost_depth (outside : List ℕ) (x : ι → ℝ) (K : ℝ)
    (hK : 1 ≤ K) (hx : ∀ j, 0 < x j) (houtside : ∀ q ∈ outside, 0 < q)
    (N d : ℕ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (hc : TreeCostLe N h e) (hd : TreeDepth d h e) (ha : TreeSmallAtoms h e)
    (hr : TreeRelativeControl x K h e) :
    TreeDerivativeBudget outside x K ((N:ℝ)*K^d) h e := by
  induction h with
  | leaf a =>
    refine ⟨e.periodExpr_relativeControl outside x K hr ha hx houtside,
      e.periodExpr_budget_le outside N d hK hc hd,?_⟩
    have hlen : (a.small.length:ℝ) ≤ N := by exact_mod_cast (StateSmallAtoms.length_le_cost e ha).trans hc
    exact hlen.trans (le_mul_of_one_le_right (Nat.cast_nonneg N) (one_le_pow₀ hK))
  | @node l a p u hp hm left right il ir =>
    exact ⟨(treeRelativeControl_root x K left e.2.1 hr.2.1).1,
      (treeBudgetLe_root K _ left e.2.1 (tree_budget_le hK N d left e.2.1 hc.2.1 hd.2.1)).1,
      il e.2.1 hc.2.1 hd.2.1 ha.2.1 hr.2.1,
      ir e.2.2 hc.2.2 hd.2.2 ha.2.2 hr.2.2⟩

theorem symbolicHistory_derivativeBudget (K : ℝ) (hK : 1 ≤ K)
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ} (h : History l) (hs : h.Supported V outside)
    (x : HistoryOccurrenceVariables.Key h → ℝ) (hx : ∀ j, 0 < x j)
    (houtside : ∀ q ∈ outside, 0 < q)
    (hr : TreeRelativeControl x K h (symbolicHistory h hs)) :
    TreeDerivativeBudget outside x K
      ((2^l*(2+h.root.small.length+2*h.internalOccurrences.length):ℕ)*K^l)
      h (symbolicHistory h hs) :=
  treeDerivativeBudget_of_cost_depth outside x K hK hx houtside _ l h _
    (symbolicHistory_cost_le h hs) (symbolicHistory_depth h hs) (symbolicHistory_smallAtoms h hs) hr

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
