import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsEquation48
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalFrequencyBulk
import OAI.NumberTheory.Ostmann.Construction.RemainingRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
open Arithmetic.HistoryProductWindows Characters.RationalHistory
open Arithmetic.HistorySymbolicSlots

def integerSlotExpressions (xs : List SmallSlot) : Fin xs.length → Expr Unit :=
  fun i => .fixed (xs.get i).value

theorem bulkLog_integerSlotExpressions (xs : List SmallSlot) :
    bulkLog xs (integerSlotExpressions xs) (fun _ => 0) = integerBulkLog xs := by
  have hc : Correct (fun _ : Unit => (0:ℚ)) xs (integerSlotExpressions xs) := by
    intro i
    exact ⟨trivial,by simp [integerSlotExpressions,Expr.rationalEval]⟩
  exact bulkLog_correct_integer _ _ hc

theorem realProduct_integerSlotExpressions (xs : List SmallSlot) :
    realProduct xs (integerSlotExpressions xs) (fun _ => 0) = ((xs.map SmallSlot.value).prod:ℝ) := by
  simp only [realProduct,integerSlotExpressions,Expr.realEval,Int.cast_natCast]
  have he := congrArg (fun ns : List ℕ => (ns.prod:ℝ)) (List.ofFn_getElem_eq_map xs SmallSlot.value)
  simpa only [List.prod_ofFn,Nat.cast_prod,List.get_eq_getElem] using he

theorem integer_half_log_bound {T : List SourceSlot} {xs : List SmallSlot}
    (hm : Template.Matches T xs) (q : ℕ) (center : ℕ → ℝ) (G B E : ℝ)
    (hq : 0<q) (hpos : ∀z∈xs,0<z.value)
    (hg : |Real.log (q:ℝ)-G| ≤ 1) (hb : |integerBulkLog xs-B| ≤ E)
    (hcell : ∀z∈xs,z.role ≠ .bulk → |Real.log (z.value:ℝ)-center z.origin| ≤ 1) :
    |Real.log (halfProduct q xs:ℝ)-(G+B+sourceSum (fixedCenter center) T)| ≤
      1+E+sourceSum fixedCount T := by
  have he := halfProduct_log_bound hm (.fixed q : Expr Unit) (integerSlotExpressions xs) (fun _ => 0)
    center G B E (by simpa [Expr.realEval] using (show (0:ℝ)<q by exact_mod_cast hq))
    (fun i => by simpa [integerSlotExpressions,Expr.realEval] using
      (show (0:ℝ)<(xs.get i).value by exact_mod_cast hpos _ (List.get_mem xs i)))
    (by simpa [Expr.realEval] using hg)
    (by simpa only [bulkLog_integerSlotExpressions] using hb)
    (fun i hi => by simpa [integerSlotExpressions,Expr.realEval] using hcell _ (List.get_mem xs i) hi)
  simpa only [Arithmetic.HistoryProductWindows.halfProduct,realProduct_integerSlotExpressions,
    Expr.realEval,Int.cast_natCast,halfProduct,Nat.cast_mul] using he

theorem integer_compensation_log_bound {T : List SourceSlot} {u : List SmallSlot}
    (j : ℕ) (hm : Template.Matches T u) (hu : ∀z∈u,z.role = .compensation j)
    (center : ℕ → ℝ) (hpos : ∀z∈u,0<z.value)
    (hcell : ∀z∈u,|Real.log (z.value:ℝ)-center z.origin| ≤ 1) :
    |Real.log ((u.map SmallSlot.value).prod:ℝ)-sourceSum (fixedCenter center) T| ≤ sourceSum fixedCount T := by
  have he := compensation_log_bound j hm hu (integerSlotExpressions u) (fun _ => 0) center
    (fun i => by simpa [integerSlotExpressions,Expr.realEval] using
      (show (0:ℝ)<(u.get i).value by exact_mod_cast hpos _ (List.get_mem u i)))
    (fun i => by simpa [integerSlotExpressions,Expr.realEval] using hcell _ (List.get_mem u i))
  simpa only [realProduct_integerSlotExpressions] using he

theorem actualCoefficient_remaining_window (sources : SourceFamily) (b s k l : ℕ)
    (V : ℕ → ℕ) (X G tb td : ℝ) (g : (p:ℕ) → ZMod p → ℂ) (outside : List ℕ)
    (a : State) (u hs : List SmallSlot) (q : ℕ) (center : ℕ → ℝ)
    (ha : Template.Matches (Template.current (Template.initial (2*b) k) l) a.small)
    (hA : actualCoefficient sources (Template.initial (2*b) k) V X G g
      (Arithmetic.sourceStateBins b s tb td) outside l a ≠ 0)
    (hperm : a.small.Perm (u++hs)) (hu : ∀z∈u,z.role = .compensation (l+1))
    (hm : Template.Matches (Template.remainder (l+1)
      (Template.current (Template.initial (2*b) k) l)) hs)
    (hq : 0<q) (hpos : ∀z∈hs,0<z.value) (hg : |Real.log (q:ℝ)-G| ≤ 1)
    (hcell : ∀z∈hs,z.role ≠ .bulk → |Real.log (z.value:ℝ)-center z.origin| ≤ 1) :
    |Real.log (halfProduct q hs:ℝ)-(G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center))| ≤
      inheritedWidth k l := by
  have hb := actualCoefficient_integerBulkLog_bound sources b s k V X G tb td g outside l a ha hA
  rw [integerBulkLog_perm hperm,integerBulkLog_append,integerBulkLog_compensation (l+1) u hu,zero_add] at hb
  have he := integer_half_log_bound hm q center G ((2:ℝ)^l*(2*tb)) ((2:ℝ)^l*2)
    hq hpos hg hb hcell
  have hC : sourceSum (fixedCenter center) (Template.remainder (l+1)
      (Template.current (Template.initial (2*b) k) l)) = (2:ℝ)^l*inheritedCenter b k l center := by
    exact sourceSum_current_filter (fixedCenter center) _ _ l
  have hN := fixedCount_current_filter_le (fun z => decide (z.role ≠ .compensation (l+1))) (2*b) k l
  rw [hC] at he
  have hid : G+(2:ℝ)^l*(2*tb)+(2:ℝ)^l*inheritedCenter b k l center =
      G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center) := by ring
  rw [hid] at he
  change sourceSum fixedCount (Template.remainder (l+1) (Template.current (Template.initial (2*b) k) l)) ≤ _ at hN
  exact he.trans (by unfold inheritedWidth; nlinarith)

theorem integer_removed_window (b k l : ℕ) (u : List SmallSlot) (center : ℕ → ℝ)
    (hu : ∀z∈u,z.role = .compensation (l+1))
    (hm : Template.Matches (Template.extracted (l+1)
      (Template.current (Template.initial (2*b) k) l)) u)
    (hpos : ∀z∈u,0<z.value)
    (hcell : ∀z∈u,|Real.log (z.value:ℝ)-center z.origin| ≤ 1) :
    |Real.log ((u.map SmallSlot.value).prod:ℝ)-(2:ℝ)^l*removedCenter b k l center| ≤ removedWidth k l := by
  have he := integer_compensation_log_bound (l+1) hm hu center hpos hcell
  have hC : sourceSum (fixedCenter center) (Template.extracted (l+1)
      (Template.current (Template.initial (2*b) k) l)) = (2:ℝ)^l*removedCenter b k l center := by
    exact sourceSum_current_filter (fixedCenter center) _ _ l
  rw [hC] at he
  exact he.trans (fixedCount_current_filter_le _ (2*b) k l)

end Ostmann.Construction

end

end OAI
