import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSupport

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistoryOccurrenceVariables
variable {ι : Type*}

def AllPivots (P : ℝ→Prop) (x : ι→ℝ) :
    {l : ℕ} → (h : History l) → TreeExpr ι h → Prop
  | _, .leaf _, _ => True
  | _, .node _ _ _ _ _ left right, e =>
      P ((treeRoot left e.2.1).plus.realEval x) ∧
        AllPivots P x left e.2.1 ∧ AllPivots P x right e.2.2

def AllPivotCells (G : ℝ) (x : ι→ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h) : Prop :=
  AllPivots (fun p => 0 < p ∧ |Real.log p-G| ≤ 1) x h e

def AllPivotsPositive (x : ι→ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h) : Prop :=
  AllPivots (fun p => 0 < p) x h e

theorem AllPivots.mono {P Q : ℝ→Prop} (hPQ : ∀ p, P p→Q p)
    (x : ι→ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (he : AllPivots P x h e) : AllPivots Q x h e := by
  induction h with
  | leaf a => trivial
  | node a p u hp hm left right il ir =>
      exact ⟨hPQ _ he.1,il e.2.1 he.2.1,ir e.2.2 he.2.2⟩

theorem AllPivotCells.positive {G : ℝ} {x : ι→ℝ} {l : ℕ}
    {h : History l} {e : TreeExpr ι h} (he : AllPivotCells G x h e) :
    AllPivotsPositive x h e :=
  AllPivots.mono (fun _ hp => hp.1) x h e he

theorem allPivotCells_of_support_ne_zero (b s : ℕ) (tb td G : ℝ)
    (outside : List ℕ) (x : ι→ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (hz : realHistorySupportWeight b s tb td G outside x h e ≠ 0) :
    AllPivotCells G x h e := by
  induction h with
  | leaf a => trivial
  | node a p u hp hm left right il ir =>
      have hn :
          (giantCell G ((treeRoot left e.2.1).plus.realEval x) ≠ 0 ∧
            realHistorySupportWeight b s tb td G outside x left e.2.1 ≠ 0) ∧
            realHistorySupportWeight b s tb td G outside x right e.2.2 ≠ 0 := by
        simpa only [realHistorySupportWeight,mul_ne_zero_iff] using hz
      exact ⟨giantCell_ne_zero_support G _ hn.1.1,il e.2.1 hn.1.2,ir e.2.2 hn.2⟩

theorem allPivotCells_of_realHistoryScalar_ne_zero (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) (x : ι→ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (hz : realHistoryScalar b s X tb td G outside x h e ≠ 0) :
    AllPivotCells G x h e :=
  allPivotCells_of_support_ne_zero b s tb td G outside x h e
    (realHistorySupportWeight_ne_zero_of_scalar_ne_zero b s X tb td G outside x h e hz)

theorem allPivotsPositive_of_realHistoryScalar_ne_zero (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) (x : ι→ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (hz : realHistoryScalar b s X tb td G outside x h e ≠ 0) :
    AllPivotsPositive x h e :=
  (allPivotCells_of_realHistoryScalar_ne_zero b s X tb td G outside x h e hz).positive

theorem realHistoryScalar_eq_zero_of_not_allPivotCells (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) (x : ι→ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (hn : ¬AllPivotCells G x h e) :
    realHistoryScalar b s X tb td G outside x h e = 0 := by
  by_contra hz
  exact hn (allPivotCells_of_realHistoryScalar_ne_zero b s X tb td G outside x h e hz)

theorem realHistoryScalar_eq_zero_of_not_allPivotsPositive (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) (x : ι→ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (hn : ¬AllPivotsPositive x h e) :
    realHistoryScalar b s X tb td G outside x h e = 0 := by
  by_contra hz
  exact hn (allPivotsPositive_of_realHistoryScalar_ne_zero b s X tb td G outside x h e hz)

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
