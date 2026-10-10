import OAI.Probability.SwitchChain.PairFiberBridge

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

@[simp] theorem singletonSet_swap (G : SimpleGraph V) (i j : V) :
    singletonSet G j i = singletonSet G i j := by
  ext w
  simp only [mem_singletonSet, Outside, Xor]
  tauto

theorem leftSet_swap (G : SimpleGraph V) (i j : V) :
    leftSet G j i = singletonSet G i j \ leftSet G i j := by
  classical
  ext w
  simp only [mem_leftSet, Finset.mem_sdiff, mem_singletonSet, Outside, Xor]
  tauto

theorem leftSet_card_swap (G : SimpleGraph V) (i j : V) :
    (leftSet G j i).card = (singletonSet G i j).card - (leftSet G i j).card := by
  classical
  rw [leftSet_swap, Finset.card_sdiff_of_subset (leftSet_subset_singletonSet G i j)]

def assignmentReverse (G : SimpleGraph V) (i j : V) :
    Assignment G i j ≃ Assignment G j i where
  toFun T := ⟨singletonSet G i j \ T.val, by
    constructor
    · exact (Finset.sdiff_subset).trans (singletonSet_swap G i j).symm.subset
    · rw [Finset.card_sdiff_of_subset T.property.1, T.property.2]
      exact (leftSet_card_swap G i j).symm⟩
  invFun T := ⟨singletonSet G j i \ T.val, by
    constructor
    · exact (Finset.sdiff_subset).trans (singletonSet_swap G i j).subset
    · rw [Finset.card_sdiff_of_subset T.property.1, T.property.2]
      exact (leftSet_card_swap G j i).symm⟩
  left_inv T := by
    apply Subtype.ext
    change singletonSet G j i \ (singletonSet G i j \ T.val) = T.val
    rw [singletonSet_swap]
    exact Finset.sdiff_sdiff_eq_self T.property.1
  right_inv T := by
    apply Subtype.ext
    change singletonSet G i j \ (singletonSet G j i \ T.val) = T.val
    rw [← singletonSet_swap G i j]
    exact Finset.sdiff_sdiff_eq_self T.property.1

@[simp] theorem assignmentReverse_val (G : SimpleGraph V) (i j : V)
    (T : Assignment G i j) :
    (assignmentReverse G i j T).val = singletonSet G i j \ T.val := rfl

theorem trade_reverse (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Assignment G i j) :
    trade G j i hij.symm (assignmentReverse G i j T).val
      (assignmentReverse G i j T).property.1 =
      trade G i j hij T.val T.property.1 := by
  apply graph_eq_of_key_leftSet_eq (i := j) (j := i)
  · calc
      key j i _ = key j i G := key_trade _ _ _ _ _ _
      _ = key i j G := key_swap G j i
      _ = key i j _ := (key_trade G i j hij T.val T.property.1).symm
      _ = key j i _ := key_swap _ i j
  · simp only [leftSet_trade, assignmentReverse_val,
      leftSet_swap (trade G i j hij T.val T.property.1) i j,
      singletonSet_eq_of_key_eq (key_trade G i j hij T.val T.property.1)]

theorem assignment_equal_reverse (G : SimpleGraph V) (i j k l : V)
    (hk : k ∈ singletonSet G i j) (hl : l ∈ singletonSet G i j)
    (T : Assignment G i j) :
    (k ∈ (assignmentReverse G i j T).val ↔ l ∈ (assignmentReverse G i j T).val) ↔
      (k ∈ T.val ↔ l ∈ T.val) := by
  simp only [assignmentReverse_val, Finset.mem_sdiff, hk, hl, true_and]
  tauto

theorem singleton_adj_equal_swap (G : SimpleGraph V) (i j k l : V)
    (hk : k ∈ singletonSet G i j) (hl : l ∈ singletonSet G i j) :
    (G.Adj i k ↔ G.Adj i l) ↔ (G.Adj j k ↔ G.Adj j l) := by
  have hk' := (mem_singletonSet G i j k).mp hk
  have hl' := (mem_singletonSet G i j l).mp hl
  simp only [Xor] at hk' hl'
  tauto

theorem singleton_equality_indicator_swap (G : SimpleGraph V) (i j k l : V) :
    (if k ∈ singletonSet G i j ∧ l ∈ singletonSet G i j then
      if G.Adj i k ↔ G.Adj i l then (1 : ℝ) else 0 else 0) =
    (if k ∈ singletonSet G j i ∧ l ∈ singletonSet G j i then
      if G.Adj j k ↔ G.Adj j l then (1 : ℝ) else 0 else 0) := by
  simp only [singletonSet_swap]
  by_cases h : k ∈ singletonSet G i j ∧ l ∈ singletonSet G i j
  · simp only [h, singleton_adj_equal_swap G i j k l h.1 h.2]
  · simp only [h, ite_false]

theorem stateFiberEquiv_reverse {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (T : Assignment G.val i j) :
    ((stateFiberEquiv G j i hij.symm).symm
      (assignmentReverse G.val i j T)).val =
      ((stateFiberEquiv G i j hij).symm T).val := by
  apply Subtype.ext
  exact trade_reverse G.val i j hij T

theorem sum_assignment_reverse {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : GraphState n d → ℝ) :
    (∑ T : Assignment G.val j i, f ((stateFiberEquiv G j i hij.symm).symm T).val) =
      ∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val := by
  classical
  rw [← (assignmentReverse G.val i j).sum_comp]
  apply Finset.sum_congr rfl
  intro T _
  rw [stateFiberEquiv_reverse]

end Problem315.PairFiber

end

end OAI
