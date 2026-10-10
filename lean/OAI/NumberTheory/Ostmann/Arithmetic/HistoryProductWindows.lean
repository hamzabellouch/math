import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsCells
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsSupport

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryProductWindows
open Construction Characters.RationalHistory HistorySymbolicSlots HistorySymbolicState
open HistorySymbolicEncoding HistoryOccurrenceVariables
variable {ι : Type*}

def inheritedCenter (b k l : ℕ) (center : ℕ → ℝ) : ℝ :=
  sourceSum (fixedCenter center) (pruned (Template.initial (2*b) k) (l+1))

def removedCenter (b k l : ℕ) (center : ℕ → ℝ) : ℝ :=
  sourceSum (fixedCenter center)
    (Template.extracted (l+1) (pruned (Template.initial (2*b) k) l))

def inheritedWidth (k l : ℕ) : ℝ := 1+(2:ℝ)^l*(8+4*(k:ℝ))
def removedWidth (k l : ℕ) : ℝ := (2:ℝ)^l*(6+4*(k:ℝ))

variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem left_inherited_window (b s k : ℕ) (tb td G : ℝ) (center : ℕ → ℝ) (x : ι → ℝ)
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : InternalKey (History.node a p u hp hm left right) → Expr ι)
    (hb : LeafBins b s k tb td outside x (History.node a p u hp hm left right)
      (encode V outside (History.node a p u hp hm left right) hs e comp))
    (hmatch : Template.Matches
      (Template.remainder (l+1) (Template.current (Template.initial (2*b) k) l)) hp)
    (hgpos : 0 < e.plus.realEval x)
    (hpos : ∀i,0 < (leftPart (splitSlots hs e) i).realEval x)
    (hg : |Real.log (e.plus.realEval x)-G| ≤ 1)
    (hcell : ∀i,(hp.get i).role ≠ .bulk →
      |Real.log ((leftPart (splitSlots hs e) i).realEval x)-center (hp.get i).origin| ≤ 1) :
    |Real.log (halfProduct e.plus hp (leftPart (splitSlots hs e)) x) -
      (G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center))| ≤ inheritedWidth k l := by
  have hbulk := inherited_bulkLog_bound b s k tb td x left (History.supported_left hs)
    (leftState hs e (fun i => comp (Sum.inl i)))
    (fun i => comp (Sum.inr (Sum.inl i))) hb.1
  rw [(bulkLog_children hs e (fun i => comp (Sum.inl i)) x).1] at hbulk
  have he := halfProduct_log_bound hmatch e.plus _ x center G ((2:ℝ)^l*(2*tb))
    ((2:ℝ)^l*2) hgpos hpos hg hbulk hcell
  have hcenter : sourceSum (fixedCenter center)
      (Template.remainder (l+1) (Template.current (Template.initial (2*b) k) l)) =
      (2:ℝ)^l * inheritedCenter b k l center := by
    simpa only [Template.remainder, inheritedCenter, pruned] using
      sourceSum_current_filter (fixedCenter center) (fun q => decide (q.role ≠ .compensation (l+1)))
        (Template.initial (2*b) k) l
  have hcount := fixedCount_current_filter_le (fun q => decide (q.role ≠ .compensation (l+1))) (2*b) k l
  change sourceSum fixedCount (Template.remainder (l+1) (Template.current (Template.initial (2*b) k) l)) ≤
    (2:ℝ)^l*(6+4*(k:ℝ)) at hcount
  rw [hcenter] at he
  have harg : G+(2:ℝ)^l*(2*tb)+(2:ℝ)^l*inheritedCenter b k l center =
      G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center) := by ring
  rw [harg] at he
  exact he.trans (by unfold inheritedWidth; linarith)

theorem right_inherited_window (b s k : ℕ) (tb td G : ℝ) (center : ℕ → ℝ) (x : ι → ℝ)
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : InternalKey (History.node a p u hp hm left right) → Expr ι)
    (hb : LeafBins b s k tb td outside x (History.node a p u hp hm left right)
      (encode V outside (History.node a p u hp hm left right) hs e comp))
    (hmatch : Template.Matches
      (Template.remainder (l+1) (Template.current (Template.initial (2*b) k) l)) hm)
    (hgpos : 0 < e.minus.realEval x)
    (hpos : ∀i,0 < (rightPart (splitSlots hs e) i).realEval x)
    (hg : |Real.log (e.minus.realEval x)-G| ≤ 1)
    (hcell : ∀i,(hm.get i).role ≠ .bulk →
      |Real.log ((rightPart (splitSlots hs e) i).realEval x)-center (hm.get i).origin| ≤ 1) :
    |Real.log (halfProduct e.minus hm (rightPart (splitSlots hs e)) x) -
      (G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center))| ≤ inheritedWidth k l := by
  have hbulk := inherited_bulkLog_bound b s k tb td x right (History.supported_right hs)
    (rightState hs e (fun i => comp (Sum.inl i)))
    (fun i => comp (Sum.inr (Sum.inr i))) hb.2
  rw [(bulkLog_children hs e (fun i => comp (Sum.inl i)) x).2] at hbulk
  have he := halfProduct_log_bound hmatch e.minus _ x center G ((2:ℝ)^l*(2*tb))
    ((2:ℝ)^l*2) hgpos hpos hg hbulk hcell
  have hcenter : sourceSum (fixedCenter center)
      (Template.remainder (l+1) (Template.current (Template.initial (2*b) k) l)) =
      (2:ℝ)^l * inheritedCenter b k l center := by
    simpa only [Template.remainder, inheritedCenter, pruned] using
      sourceSum_current_filter (fixedCenter center) (fun q => decide (q.role ≠ .compensation (l+1)))
        (Template.initial (2*b) k) l
  have hcount := fixedCount_current_filter_le (fun q => decide (q.role ≠ .compensation (l+1))) (2*b) k l
  change sourceSum fixedCount (Template.remainder (l+1) (Template.current (Template.initial (2*b) k) l)) ≤
    (2:ℝ)^l*(6+4*(k:ℝ)) at hcount
  rw [hcenter] at he
  have harg : G+(2:ℝ)^l*(2*tb)+(2:ℝ)^l*inheritedCenter b k l center =
      G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center) := by ring
  rw [harg] at he
  exact he.trans (by unfold inheritedWidth; linarith)

theorem removed_window (b k : ℕ) (center : ℕ → ℝ) (x : ι → ℝ)
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (comp : Fin u.length → Expr ι)
    (hmatch : Template.Matches
      (Template.extracted (l+1) (Template.current (Template.initial (2*b) k) l)) u)
    (hpos : ∀i,0 < (comp i).realEval x)
    (hcell : ∀i,|Real.log ((comp i).realEval x)-center (u.get i).origin| ≤ 1) :
    |Real.log (realProduct u comp x)-(2:ℝ)^l*removedCenter b k l center| ≤ removedWidth k l := by
  have he := compensation_log_bound (l+1) hmatch (History.supported_compensation_roles hs)
    comp x center hpos hcell
  have hcenter : sourceSum (fixedCenter center)
      (Template.extracted (l+1) (Template.current (Template.initial (2*b) k) l)) =
      (2:ℝ)^l*removedCenter b k l center := by
    exact sourceSum_current_filter (fixedCenter center) _ _ l
  rw [hcenter] at he
  exact he.trans (fixedCount_current_filter_le _ (2*b) k l)

end Ostmann.Arithmetic.HistoryProductWindows

end

end OAI
