import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsSlots
import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplate

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryProductWindows
open Construction Characters.RationalHistory HistorySymbolicSlots HistorySymbolicState
open HistorySymbolicEncoding HistoryOccurrenceVariables
open Construction.InitialCoordinatesTemplate
variable {ι : Type*}

theorem initial_bulkLog (b k : ℕ) (a : State)
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (f : Fin a.small.length → Expr ι) (x : ι → ℝ) :
    bulkLog a.small f x =
      (∑i, if sourceBulkHalf b false (a.small.get i) then Real.log ((f i).realEval x) else 0) +
      (∑i, if sourceBulkHalf b true (a.small.get i) then Real.log ((f i).realEval x) else 0) := by
  unfold bulkLog slotSum
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨ho,hr⟩ := matches_initial_metadata ha i
  by_cases hb : (a.small.get i).role = .bulk
  · have hi := hr.mp hb
    by_cases hh : i.val < b
    · simp only [sourceBulkHalf, hb, ho, true_and, Bool.false_eq_true, ↓reduceIte,
        ite_eq_left hh, ite_eq_right (show ¬(b ≤ i.val ∧ i.val < 2*b) by omega), add_zero]
    · simp only [sourceBulkHalf, hb, ho, true_and, Bool.false_eq_true, ↓reduceIte,
        ite_eq_right hh, ite_eq_left (show b ≤ i.val ∧ i.val < 2*b by omega), zero_add]
  · simp only [sourceBulkHalf, hb, false_and, ↓reduceIte, add_zero]

theorem initial_bulkLog_bound (b s k : ℕ) (a : State) (outside : List ℕ)
    (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (f : Fin a.small.length → Expr ι) (x : ι → ℝ) (tb td : ℝ)
    (hb : realStateBins b s tb td a outside (fun i => (f i).realEval x)
      (fun i => (outside.get i : ℝ)) ≠ 0) : |bulkLog a.small f x - 2*tb| ≤ 2 := by
  have hf := (realStateBins_support b s tb td a outside _ _ hb false).1
  have ht := (realStateBins_support b s tb td a outside _ _ hb true).1
  rw [initial_bulkLog b k a ha]
  have he := abs_add_le
    ((∑i,if sourceBulkHalf b false (a.small.get i) then Real.log ((f i).realEval x) else 0)-tb)
    ((∑i,if sourceBulkHalf b true (a.small.get i) then Real.log ((f i).realEval x) else 0)-tb)
  have hid : (∑i,if sourceBulkHalf b false (a.small.get i) then Real.log ((f i).realEval x) else 0) +
      (∑i,if sourceBulkHalf b true (a.small.get i) then Real.log ((f i).realEval x) else 0) - 2*tb =
    ((∑i,if sourceBulkHalf b false (a.small.get i) then Real.log ((f i).realEval x) else 0)-tb) +
    ((∑i,if sourceBulkHalf b true (a.small.get i) then Real.log ((f i).realEval x) else 0)-tb) := by ring
  rw [hid]
  linarith

def LeafBins (b s k : ℕ) (tb td : ℝ) (outside : List ℕ) (x : ι → ℝ) :
    {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf a, e => Template.Matches (Template.initial (2*b) k) a.small ∧
      realStateBins b s tb td a outside (fun i => (e.small i).realEval x)
        (fun i => (outside.get i : ℝ)) ≠ 0
  | _, .node _ _ _ _ _ left right, e =>
      LeafBins b s k tb td outside x left e.2.1 ∧ LeafBins b s k tb td outside x right e.2.2

theorem inherited_bulkLog_bound (b s k : ℕ) (tb td : ℝ) (x : ι → ℝ)
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι)
    (hb : LeafBins b s k tb td outside x h (encode V outside h hs e comp)) :
    |bulkLog h.root.small e.small x - (2:ℝ)^l * (2*tb)| ≤ (2:ℝ)^l * 2 := by
  induction h with
  | leaf a =>
    simpa only [History.root, pow_zero, one_mul] using initial_bulkLog_bound b s k a outside hb.1 e.small x tb td hb.2
  | @node l a p u hp hm left right ihl ihr =>
    have hl := ihl (History.supported_left hs) (leftState hs e (fun i => comp (Sum.inl i)))
      (fun i => comp (Sum.inr (Sum.inl i))) hb.1
    have hr := ihr (History.supported_right hs) (rightState hs e (fun i => comp (Sum.inl i)))
      (fun i => comp (Sum.inr (Sum.inr i))) hb.2
    simp only [History.root]
    rw [bulkLog_node hs e (fun i => comp (Sum.inl i)) x]
    have he := abs_add_le
      (bulkLog left.root.small (leftState hs e (fun i => comp (Sum.inl i))).small x - (2:ℝ)^l*(2*tb))
      (bulkLog right.root.small (rightState hs e (fun i => comp (Sum.inl i))).small x - (2:ℝ)^l*(2*tb))
    rw [pow_succ]
    convert he.trans (add_le_add hl hr) using 1 <;> congr 1 <;> ring

end Ostmann.Arithmetic.HistoryProductWindows

end

end OAI
