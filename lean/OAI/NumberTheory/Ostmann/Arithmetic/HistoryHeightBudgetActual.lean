import OAI.NumberTheory.Ostmann.Arithmetic.HistoryHeightBudgetFixed

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryHeightBudgetActual
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicEncoding
open HistoryHeightBudgetFixed
variable {ι : Type*}

def StateBudgetLe (B H : ℝ) {a : State} (e : StateExpr a ι) : Prop :=
  e.plus.heightBudget B ≤ H ∧ e.minus.heightBudget B ≤ H ∧
    ∀ i, (e.small i).heightBudget B ≤ H

def TreeBudgetLe (B H : ℝ) : {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, e => StateBudgetLe B H e
  | _, .node _ _ _ _ _ left right, e =>
      StateBudgetLe B H e.1 ∧ TreeBudgetLe B H left e.2.1 ∧ TreeBudgetLe B H right e.2.2

theorem stateBudgetLe {B F : ℝ} {C D : ℕ} (hB : 1 ≤ B) {a : State} (e : StateExpr a ι)
    (hf : StateFixedBound F e) (hc : HistoryHeightBudgetCost.stateCost e ≤ C)
    (hd : HistorySymbolicCost.stateCost e ≤ D) :
    StateBudgetLe B ((2 * max 1 F)^C * B^D) e := by
  have hcp : e.plus.heightCost ≤ C := by unfold HistoryHeightBudgetCost.stateCost at hc; omega
  have hcm : e.minus.heightCost ≤ C := by unfold HistoryHeightBudgetCost.stateCost at hc; omega
  have hdp : e.plus.atomCount ≤ D := by unfold HistorySymbolicCost.stateCost at hd; omega
  have hdm : e.minus.atomCount ≤ D := by unfold HistorySymbolicCost.stateCost at hd; omega
  refine ⟨e.plus.heightBudget_le_cost hB hf.1 hcp hdp,
    e.minus.heightBudget_le_cost hB hf.2.1 hcm hdm,?_⟩
  intro i
  have hcs : (e.small i).heightCost ≤ HistoryHeightBudgetCost.slotCost e.small :=
    Finset.single_le_sum (f := fun j => (e.small j).heightCost)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hds : (e.small i).atomCount ≤ HistorySymbolicCost.slotCost e.small :=
    Finset.single_le_sum (f := fun j => (e.small j).atomCount)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  apply (e.small i).heightBudget_le_cost hB (hf.2.2 i)
  · unfold HistoryHeightBudgetCost.stateCost at hc
    omega
  · unfold HistorySymbolicCost.stateCost at hd
    omega

theorem treeBudgetLe {B F : ℝ} {C D : ℕ} (hB : 1 ≤ B) {l : ℕ}
    (h : History l) (e : TreeExpr ι h) (hf : TreeFixedBound F h e)
    (hc : HistoryHeightBudgetCost.TreeHeightCostLe C h e)
    (hd : HistorySymbolicCost.TreeCostLe D h e) :
    TreeBudgetLe B ((2 * max 1 F)^C * B^D) h e := by
  induction h with
  | leaf a => exact stateBudgetLe hB e hf hc hd
  | @node l a p u hp hm left right ihl ihr =>
    exact ⟨stateBudgetLe hB e.1 hf.1 hc.1 hd.1,
      ihl _ hf.2.1 hc.2.1 hd.2.1, ihr _ hf.2.2 hc.2.2 hd.2.2⟩

theorem coefficientHistory_heightBudget_le {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (second : Bool) {B : ℝ} (hB : 1 ≤ B) :
    TreeBudgetLe B
      ((2 * frequencyBound V l)^(2^l*(2+h.root.small.length+2*h.internalOccurrences.length+7*l)) *
        B^(2^l*(h.root.small.length+2*h.internalOccurrences.length))) h
      (HistorySymbolicLinearity.coefficientHistory h hs second) := by
  have ht := treeBudgetLe hB h _ (coefficientHistory_fixedBound h hs second)
    (HistoryHeightBudgetCost.coefficientHistory_cost_le h hs second)
    (HistoryCoefficientBounds.coefficientHistory_cost_le h hs second)
  simpa only [max_eq_right (one_le_frequencyBound V l)] using ht

theorem symbolicHistory_heightBudget_le {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) {B : ℝ} (hB : 1 ≤ B) :
    TreeBudgetLe B
      ((2 * frequencyBound V l)^(2^l*(2+h.root.small.length+2*h.internalOccurrences.length+7*l)) *
        B^(2^l*(2+h.root.small.length+2*h.internalOccurrences.length))) h
      (symbolicHistory h hs) := by
  have ht := treeBudgetLe hB h _ (symbolicHistory_fixedBound h hs)
    (HistoryHeightBudgetCost.symbolicHistory_cost_le h hs)
    (HistorySymbolicCost.symbolicHistory_cost_le h hs)
  simpa only [max_eq_right (one_le_frequencyBound V l)] using ht

end Ostmann.Arithmetic.HistoryHeightBudgetActual

end

end OAI
