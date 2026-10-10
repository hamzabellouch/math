import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsBulk
import OAI.NumberTheory.Ostmann.Construction.CoefficientSupport

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
open Arithmetic Arithmetic.HistoryProductWindows Characters.RationalHistory
open Arithmetic.HistorySymbolicSlots Arithmetic.HistorySymbolicState
open Arithmetic.HistorySymbolicEncoding Arithmetic.HistoryOccurrenceVariables
variable {ι : Type*}

def integerBulkLog (xs : List SmallSlot) : ℝ :=
  (xs.map (fun q => if q.role = .bulk then Real.log (q.value:ℝ) else 0)).sum

theorem integerBulkLog_perm {xs ys : List SmallSlot} (h : xs.Perm ys) :
    integerBulkLog xs = integerBulkLog ys := (h.map _).sum_eq

@[simp] theorem integerBulkLog_append (xs ys : List SmallSlot) :
    integerBulkLog (xs++ys) = integerBulkLog xs+integerBulkLog ys := by simp [integerBulkLog]

theorem integerBulkLog_compensation (j : ℕ) (u : List SmallSlot)
    (hu : ∀q∈u,q.role = .compensation j) : integerBulkLog u = 0 := by
  unfold integerBulkLog
  apply List.sum_eq_zero
  intro t ht
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
  rw [hu q hq]
  simp

theorem bulkLog_correct_integer {xs : List SmallSlot} (f : Fin xs.length → Expr ι)
    (x : ι → ℚ) (hf : Correct x xs f) :
    bulkLog xs f (fun i => (x i:ℝ)) = integerBulkLog xs := by
  unfold bulkLog slotSum integerBulkLog
  have he := congrArg List.sum (List.ofFn_getElem_eq_map xs
    (fun q => if q.role = .bulk then Real.log (q.value:ℝ) else 0))
  rw [List.sum_ofFn] at he
  rw [←he]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [Expr.realEval_cast_rational,(hf i).2,Rat.cast_natCast]
  rfl

theorem leafBins_correct_integer (b s k : ℕ) (tb td : ℝ) (outside : List ℕ)
    {l : ℕ} (h : History l) (e : TreeExpr ι h) (x : ι → ℚ)
    (he : TreeCorrect x h e)
    (hb : ∀a∈h.leafStates,Template.Matches (Template.initial (2*b) k) a.small ∧
      sourceStateBins b s tb td outside a ≠ 0) :
    LeafBins b s k tb td outside (fun i => (x i:ℝ)) h e := by
  induction h with
  | leaf a =>
    have ha := hb a (by simp [History.leafStates])
    refine ⟨ha.1,?_⟩
    have hs : (fun i => (e.small i).realEval (fun j => (x j:ℝ))) =
        (fun i => ((a.small.get i).value:ℝ)) := by
      funext i
      rw [Expr.realEval_cast_rational,(he.2.2.2.2 i).2,Rat.cast_natCast]
    simpa only [hs,sourceStateBins] using ha.2
  | @node l a p u hp hm left right ihl ihr =>
    exact ⟨ihl e.2.1 he.2.1 (fun a ha => hb a (by
        simpa only [History.leafStates,List.mem_append] using Or.inl ha)),
      ihr e.2.2 he.2.2 (fun a ha => hb a (by
        simpa only [History.leafStates,List.mem_append] using Or.inr ha))⟩

theorem actualCoefficient_integerBulkLog_bound (sources : SourceFamily)
    (b s k : ℕ) (V : ℕ → ℕ) (X G tb td : ℝ) (g : (p : ℕ) → ZMod p → ℂ)
    (outside : List ℕ) (l : ℕ) (a : State)
    (ha : Template.Matches (Template.current (Template.initial (2*b) k) l) a.small)
    (hA : actualCoefficient sources (Template.initial (2*b) k) V X G g
      (sourceStateBins b s tb td) outside l a ≠ 0) :
    |integerBulkLog a.small-(2:ℝ)^l*(2*tb)| ≤ (2:ℝ)^l*2 := by
  obtain ⟨c,_,hs,hb⟩ := actualCoefficient_nonzero_leaf_bins sources (Template.initial (2*b) k)
    V X G g (sourceStateBins b s tb td) outside l a ha hA
  let h := decodeHistory sources (Template.initial (2*b) k) V l a c
  have hreal := inherited_bulkLog_bound b s k tb td (fun i => (rationalSample h i:ℝ))
    h hs (rootExpr h) (compensationExpr h)
    (leafBins_correct_integer b s k tb td outside h (symbolicHistory h hs) _
      (symbolicHistory_correct h hs) hb)
  rw [bulkLog_correct_integer _ _ (rootExpr_correct h).2.2.2.2] at hreal
  simpa only [h,decodeHistory_root] using hreal

end Ostmann.Construction

end

end OAI
