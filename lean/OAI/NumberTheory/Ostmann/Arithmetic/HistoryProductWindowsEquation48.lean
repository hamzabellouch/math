import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsGeometricSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsNormalize

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryProductWindows
open Construction Characters.RationalHistory HistorySymbolicSlots HistorySymbolicState
open HistorySymbolicEncoding HistoryOccurrenceVariables InitialCoordinatesTemplate
variable {ι : Type*}
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}

theorem left_nominal_window (b s k : ℕ) (tb td G J : ℝ) (Δ : ℕ → ℝ) (center : ℕ → ℝ) (x : ι → ℝ)
    (hl : l<k)
    (htop : |(∑h,∑i,topCenters b center h i)-(J-2*tb)| ≤ 2)
    (htypes : ∀j<k,|typeCenter b j center-nominalWeight k J Δ j| ≤ 2)
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
      (G+(2:ℝ)^l*nominalWeight k J Δ l+Δ l)| ≤ nominalInheritedWidth k l := by
  apply inherited_window_normalize b k l _ G tb J (Δ l) (nominalWeight k J Δ) center
    ?_ htop htypes (nominalWeight_recurrence_scaled hl J Δ)
  exact left_inherited_window b s k tb td G center x hs e comp hb hmatch hgpos hpos hg hcell

theorem right_nominal_window (b s k : ℕ) (tb td G J : ℝ) (Δ : ℕ → ℝ) (center : ℕ → ℝ) (x : ι → ℝ)
    (hl : l<k)
    (htop : |(∑h,∑i,topCenters b center h i)-(J-2*tb)| ≤ 2)
    (htypes : ∀j<k,|typeCenter b j center-nominalWeight k J Δ j| ≤ 2)
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
      (G+(2:ℝ)^l*nominalWeight k J Δ l+Δ l)| ≤ nominalInheritedWidth k l := by
  apply inherited_window_normalize b k l _ G tb J (Δ l) (nominalWeight k J Δ) center
    ?_ htop htypes (nominalWeight_recurrence_scaled hl J Δ)
  exact right_inherited_window b s k tb td G center x hs e comp hb hmatch hgpos hpos hg hcell

theorem removed_nominal_window (b k : ℕ) (J : ℝ) (Δ : ℕ → ℝ) (center : ℕ → ℝ) (x : ι → ℝ)
    (hl : l<k)
    (htypes : ∀j<k,|typeCenter b j center-nominalWeight k J Δ j| ≤ 2)
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (comp : Fin u.length → Expr ι)
    (hmatch : Template.Matches
      (Template.extracted (l+1) (Template.current (Template.initial (2*b) k) l)) u)
    (hpos : ∀i,0 < (comp i).realEval x)
    (hcell : ∀i,|Real.log ((comp i).realEval x)-center (u.get i).origin| ≤ 1) :
    |Real.log (realProduct u comp x)-(2:ℝ)^l*nominalWeight k J Δ l| ≤ nominalRemovedWidth k l := by
  apply removed_window_normalize b k l hl _ (nominalWeight k J Δ) center ?_ htypes
  exact removed_window b k center x hs comp hmatch hpos hcell

end Ostmann.Arithmetic.HistoryProductWindows

end

end OAI
