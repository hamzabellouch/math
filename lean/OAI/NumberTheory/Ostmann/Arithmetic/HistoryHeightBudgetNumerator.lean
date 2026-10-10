import OAI.NumberTheory.Ostmann.Arithmetic.HistoryHeightBudgetActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryNumeratorForms

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryHeightBudgetNumerator
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicSlots
open HistorySymbolicNumerator HistorySymbolicEncoding HistoryNumeratorForms HistoryHeightBudgetFixed
variable {ι : Type*}

theorem numeratorExpr_heightCost (v w : ℤ) (plus minus : Expr ι) (hp hm : List (Expr ι)) :
    (numeratorExpr v w plus minus hp hm).heightCost = plus.heightCost + minus.heightCost +
      (hp.map Expr.heightCost).sum + (hm.map Expr.heightCost).sum + 5 := by
  have hP := HistoryHeightBudgetCost.product_heightCost hp
  have hM := HistoryHeightBudgetCost.product_heightCost hm
  simp only [numeratorExpr, Expr.heightCost, Expr.atomCount, Expr.fixedCount,
    Expr.fixedLiterals, List.length_append, List.length_singleton, Expr.addSubCount] at hP hM ⊢
  omega

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ} {a : State}
  {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem nodeNumerator_heightCost
    (hs : (History.node a p u hp hm left right).Supported V outside) (e : StateExpr a ι) :
    (nodeNumerator hs e).heightCost = HistoryHeightBudgetCost.stateCost e + 5 := by
  simp only [nodeNumerator,numeratorExpr_heightCost,HistoryHeightBudgetCost.sum_heightCost_ofFn]
  have hparts := HistoryHeightBudgetCost.slotCost_parts (splitSlots hs e)
  have hsplit := HistoryHeightBudgetCost.slotCost_reorder (History.supported_small_split hs) e.small
  change HistoryHeightBudgetCost.slotCost (splitSlots hs e) = HistoryHeightBudgetCost.slotCost e.small at hsplit
  unfold HistoryHeightBudgetCost.stateCost
  omega

theorem nodeNumerator_fixedBound {F : ℝ} (hF : 1 ≤ F)
    (hs : (History.node a p u hp hm left right).Supported V outside) (e : StateExpr a ι)
    (he : StateFixedBound F e) (hl : |(left.root.frequency : ℝ)| ≤ F)
    (hr : |(right.root.frequency : ℝ)| ≤ F) : (nodeNumerator hs e).FixedBound F := by
  have hP := product_ofFn_fixedBound hF (leftPart (splitSlots hs e)) (fun _ => he.2.2 _)
  have hM := product_ofFn_fixedBound hF (rightPart (splitSlots hs e)) (fun _ => he.2.2 _)
  simpa only [nodeNumerator,numeratorExpr,Expr.fixedBound_sub,Expr.fixedBound_mul,
    Expr.fixedBound_fixed] using And.intro (And.intro hl (And.intro he.2.1 hM))
      (And.intro hr (And.intro he.1 hP))

theorem nodeNumerator_heightBudget_le {B F : ℝ} {C D : ℕ} (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hs : (History.node a p u hp hm left right).Supported V outside) (e : StateExpr a ι)
    (he : StateFixedBound F e) (hl : |(left.root.frequency : ℝ)| ≤ F)
    (hr : |(right.root.frequency : ℝ)| ≤ F)
    (hc : HistoryHeightBudgetCost.stateCost e ≤ C)
    (hd : HistorySymbolicCost.stateCost e ≤ D) :
    (nodeNumerator hs e).heightBudget B ≤ (2 * max 1 F)^(C+5) * B^D := by
  apply (nodeNumerator hs e).heightBudget_le_cost hB (nodeNumerator_fixedBound hF hs e he hl hr)
  · rw [nodeNumerator_heightCost]
    omega
  · rwa [nodeNumerator_atomCount]

def TreeNodeBudgetLe (B H : ℝ) (V : ℕ → ℕ) (outside : List ℕ) :
    {l : ℕ} → (h : History l) → h.Supported V outside → TreeExpr ι h → Prop
  | _, .leaf _, _, _ => True
  | _, .node _ _ _ _ _ left right, hs, e =>
      (nodeNumerator hs e.1).heightBudget B ≤ H ∧
        TreeNodeBudgetLe B H V outside left (History.supported_left hs) e.2.1 ∧
        TreeNodeBudgetLe B H V outside right (History.supported_right hs) e.2.2

theorem treeNodeBudgetLe {B F : ℝ} {C D : ℕ} (hB : 1 ≤ B) (hF : 1 ≤ F)
    {l : ℕ} (h : History l) (hs : h.Supported V outside) (e : TreeExpr ι h)
    (hf : ∀ s ∈ h.frequencies, |(s : ℝ)| ≤ F) (he : TreeFixedBound F h e)
    (hc : HistoryHeightBudgetCost.TreeHeightCostLe C h e)
    (hd : HistorySymbolicCost.TreeCostLe D h e) :
    TreeNodeBudgetLe B ((2 * max 1 F)^(C+5) * B^D) V outside h hs e := by
  induction h with
  | leaf a => trivial
  | @node l a p u hp hm left right ihl ihr =>
    refine ⟨nodeNumerator_heightBudget_le hB hF hs e.1 he.1
      (hf _ (by simp [History.frequencies,root_frequency_mem left]))
      (hf _ (by simp [History.frequencies,root_frequency_mem right])) hc.1 hd.1,?_,?_⟩
    · exact ihl (History.supported_left hs) e.2.1
        (fun s hmem => hf s (by simp [History.frequencies,hmem])) he.2.1 hc.2.1 hd.2.1
    · exact ihr (History.supported_right hs) e.2.2
        (fun s hmem => hf s (by simp [History.frequencies,hmem])) he.2.2 hc.2.2 hd.2.2

theorem coefficientHistory_nodeNumerator_heightBudget_le {l : ℕ}
    (h : History l) (hs : h.Supported V outside) (second : Bool) {B : ℝ} (hB : 1 ≤ B) :
    TreeNodeBudgetLe B
      ((2 * frequencyBound V l)^(2^l*(2+h.root.small.length+2*h.internalOccurrences.length+7*l)+5) *
        B^(2^l*(h.root.small.length+2*h.internalOccurrences.length))) V outside h hs
      (HistorySymbolicLinearity.coefficientHistory h hs second) := by
  have ht := treeNodeBudgetLe hB (one_le_frequencyBound V l) h hs _ (supported_frequencyBound h hs)
    (coefficientHistory_fixedBound h hs second)
    (HistoryHeightBudgetCost.coefficientHistory_cost_le h hs second)
    (HistoryCoefficientBounds.coefficientHistory_cost_le h hs second)
  simpa only [max_eq_right (one_le_frequencyBound V l)] using ht

end Ostmann.Arithmetic.HistoryHeightBudgetNumerator

end

end OAI
