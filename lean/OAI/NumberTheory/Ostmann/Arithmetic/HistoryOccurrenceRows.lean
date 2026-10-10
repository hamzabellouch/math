import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCoefficientDenominators
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCoefficientIndependence
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryHeightBudgetNumerator

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryOccurrenceRows
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicState HistorySymbolicEncoding HistorySymbolicLinearity HistorySymbolicScope
open HistoryNumeratorForms HistoryCoefficientRegular HistoryCoefficientIndependence
open HistoryCoefficientDenominators HistorySymbolicCost HistoryHeightBudgetNumerator

variable {ι : Type*}

def rows (V : ℕ → ℕ) (outside : List ℕ) :
    {l : ℕ} → (h : History l) → h.Supported V outside → TreeExpr ι h → TreeExpr ι h →
      InternalKey h → Expr ι × Expr ι
  | _, .leaf _, _, _, _ => fun i => nomatch i
  | _, .node _ _ _ _ _ left right, hs, c, d =>
      Sum.elim (fun _ => (nodeNumerator hs c.1,nodeNumerator hs d.1))
        (Sum.elim (rows V outside left (History.supported_left hs) c.2.1 d.2.1)
          (rows V outside right (History.supported_right hs) c.2.2 d.2.2))

theorem rows_regular {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (c d : TreeExpr ι h) (x : ι → ℚ)
    (hc : TreeRegular x h c) (hd : TreeRegular x h d) (i : InternalKey h) :
    (rows V outside h hs c d i).1.RegularAt x ∧
      (rows V outside h hs c d i).2.RegularAt x := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      rcases i with i | i
      · exact ⟨nodeNumerator_regular hs c.1 x hc.1,nodeNumerator_regular hs d.1 x hd.1⟩
      · rcases i with i | i
        · exact ihl (History.supported_left hs) c.2.1 d.2.1 hc.2.1 hd.2.1 i
        · exact ihr (History.supported_right hs) c.2.2 d.2.2 hc.2.2 hd.2.2 i

theorem rows_nonzero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (c d : TreeExpr ι h) (x : ι → ℚ)
    (hc : TreeIndependent x h c d) (i : InternalKey h) :
    (rows V outside h hs c d i).1.rationalEval x ≠ 0 ∨
      (rows V outside h hs c d i).2.rationalEval x ≠ 0 := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      rcases i with i | i
      · exact nodeNumerator_row_ne_zero hs c.1 d.1 x hc.1
      · rcases i with i | i
        · exact ihl (History.supported_left hs) c.2.1 d.2.1 hc.2.1 i
        · exact ihr (History.supported_right hs) c.2.2 d.2.2 hc.2.2 i

theorem rows_above {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (c d : TreeExpr ι h) (level : ι → ℕ)
    (hc : TreeAbove level h c) (hd : TreeAbove level h d) (i : InternalKey h) :
    Above level (internalLevel h i) (rows V outside h hs c d i).1 ∧
      Above level (internalLevel h i) (rows V outside h hs c d i).2 := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      rcases i with i | i
      · exact ⟨nodeNumerator_above hs c.1 level hc.1,nodeNumerator_above hs d.1 level hd.1⟩
      · rcases i with i | i
        · exact ihl (History.supported_left hs) c.2.1 d.2.1 hc.2.1 hd.2.1 i
        · exact ihr (History.supported_right hs) c.2.2 d.2.2 hc.2.2 hd.2.2 i

theorem rows_safe {S : Set ℤ} {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (c d : TreeExpr ι h)
    (hc : TreeSafe S h c) (hd : TreeSafe S h d) (i : InternalKey h) :
    SafeRationalExpressions.Expression S (rows V outside h hs c d i).1 ∧
      SafeRationalExpressions.Expression S (rows V outside h hs c d i).2 := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      rcases i with i | i
      · exact ⟨nodeNumerator_safe hs c.1 hc.1,nodeNumerator_safe hs d.1 hd.1⟩
      · rcases i with i | i
        · exact ihl (History.supported_left hs) c.2.1 d.2.1 hc.2.1 hd.2.1 i
        · exact ihr (History.supported_right hs) c.2.2 d.2.2 hc.2.2 hd.2.2 i

theorem rows_atomCount {C D : ℕ} {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (c d : TreeExpr ι h)
    (hc : TreeCostLe C h c) (hd : TreeCostLe D h d) (i : InternalKey h) :
    (rows V outside h hs c d i).1.atomCount ≤ C ∧
      (rows V outside h hs c d i).2.atomCount ≤ D := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      rcases i with i | i
      · simpa only [rows,Sum.elim_inl,nodeNumerator_atomCount] using And.intro hc.1 hd.1
      · rcases i with i | i
        · exact ihl (History.supported_left hs) c.2.1 d.2.1 hc.2.1 hd.2.1 i
        · exact ihr (History.supported_right hs) c.2.2 d.2.2 hc.2.2 hd.2.2 i

theorem rows_heightBudget {B H : ℝ} {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (c d : TreeExpr ι h)
    (hc : TreeNodeBudgetLe B H V outside h hs c)
    (hd : TreeNodeBudgetLe B H V outside h hs d) (i : InternalKey h) :
    (rows V outside h hs c d i).1.heightBudget B ≤ H ∧
      (rows V outside h hs c d i).2.heightBudget B ≤ H := by
  induction h with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
      rcases i with i | i
      · exact ⟨hc.1,hd.1⟩
      · rcases i with i | i
        · exact ihl (History.supported_left hs) c.2.1 d.2.1 hc.2.1 hd.2.1 i
        · exact ihr (History.supported_right hs) c.2.2 d.2.2 hc.2.2 hd.2.2 i

def canonical {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) : InternalKey h → Expr (Key h) × Expr (Key h) :=
  rows V outside h hs (coefficientHistory h hs false) (coefficientHistory h hs true)

theorem canonical_regular_nonzero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    (canonical h hs i).1.RegularAt (rationalSample h) ∧
    (canonical h hs i).2.RegularAt (rationalSample h) ∧
    ((canonical h hs i).1.rationalEval (rationalSample h) ≠ 0 ∨
      (canonical h hs i).2.rationalEval (rationalSample h) ≠ 0) :=
  ⟨(rows_regular h hs _ _ _ (coefficientHistory_regular h hs false)
      (coefficientHistory_regular h hs true) i).1,
    (rows_regular h hs _ _ _ (coefficientHistory_regular h hs false)
      (coefficientHistory_regular h hs true) i).2,
    rows_nonzero h hs _ _ _ (coefficientHistory_independent h hs) i⟩

theorem canonical_above {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    Above (keyLevel h) (internalLevel h i) (canonical h hs i).1 ∧
      Above (keyLevel h) (internalLevel h i) (canonical h hs i).2 :=
  rows_above h hs _ _ _ (HistoryCoefficientBounds.coefficientHistory_above h hs false)
    (HistoryCoefficientBounds.coefficientHistory_above h hs true) i

theorem canonical_safe {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    SafeRationalExpressions.Expression {s | s ∈ h.frequencies} (canonical h hs i).1 ∧
      SafeRationalExpressions.Expression {s | s ∈ h.frequencies} (canonical h hs i).2 :=
  rows_safe h hs _ _ (coefficientHistory_safe h hs false) (coefficientHistory_safe h hs true) i

theorem canonical_atomCount {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    (canonical h hs i).1.atomCount ≤ 2^l*(h.root.small.length+2*h.internalOccurrences.length) ∧
      (canonical h hs i).2.atomCount ≤ 2^l*(h.root.small.length+2*h.internalOccurrences.length) :=
  rows_atomCount h hs _ _ (HistoryCoefficientBounds.coefficientHistory_cost_le h hs false)
    (HistoryCoefficientBounds.coefficientHistory_cost_le h hs true) i

theorem canonical_heightBudget {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) {B : ℝ} (hB : 1 ≤ B) :
    let H := (2*HistoryHeightBudgetFixed.frequencyBound V l)^
      (2^l*(2+h.root.small.length+2*h.internalOccurrences.length+7*l)+5)*
      B^(2^l*(h.root.small.length+2*h.internalOccurrences.length))
    (canonical h hs i).1.heightBudget B ≤ H ∧ (canonical h hs i).2.heightBudget B ≤ H :=
  rows_heightBudget h hs _ _ (coefficientHistory_nodeNumerator_heightBudget_le h hs false hB)
    (coefficientHistory_nodeNumerator_heightBudget_le h hs true hB) i

end Ostmann.Arithmetic.HistoryOccurrenceRows

end

end OAI
