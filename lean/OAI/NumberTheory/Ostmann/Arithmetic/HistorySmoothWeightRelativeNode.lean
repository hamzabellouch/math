import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsGeometricSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightLabels
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRelativePivot

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicSlots
open HistoryOccurrenceVariables HistoryProductWindows
variable {ι : Type*}

theorem atomSlots_positive_cells (slot : ι → Option SmallSlot) (center : ℕ → ℝ)
    (x : ι → ℝ) (hx : ∀ j, 0 < x j) (hsource : IndependentSourceCells slot center x)
    (xs : List SmallSlot) (f : Fin xs.length → Expr ι) (hf : AtomSlotsCorrect slot xs f) :
    (∀ i, 0 < (f i).realEval x) ∧
      (∀ i, (xs.get i).role ≠ .bulk →
        |Real.log ((f i).realEval x) - center (xs.get i).origin| ≤ 1) := by
  constructor
  · intro i
    obtain ⟨j,hj,hslot⟩ := hf i
    rw [hj]
    exact hx j
  · intro i hi
    obtain ⟨j,hj,hslot⟩ := hf i
    rw [hj]
    exact hsource j _ hslot hi

theorem source_node_relativeControl (b s k : ℕ) (tb td G K : ℝ)
    (center : ℕ → ℝ) (slot : ι → Option SmallSlot) (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hsource : IndependentSourceCells slot center x)
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hlabels : TreeSourceLabels (Template.initial (2*b) k) (History.node a p u hp hm left right))
    (e : StateExpr a ι) (comp : InternalKey (History.node a p u hp hm left right) → Expr ι)
    (he : StateAtomSlots slot e)
    (hc : ∀ i, ∃ j, comp i = .atom j ∧ slot j = some (internalSlot _ i))
    (her : e.plus.RelativeControl x K ∧ e.minus.RelativeControl x K)
    (hplus : 0 < e.plus.realEval x) (hminus : 0 < e.minus.realEval x)
    (hgp : |Real.log (e.plus.realEval x)-G| ≤ 1)
    (hgm : |Real.log (e.minus.realEval x)-G| ≤ 1)
    (hsupport : realHistorySupportWeight b s tb td G outside x
      (History.node a p u hp hm left right) (encode V outside _ hs e comp) ≠ 0)
    (hK : Real.exp (sourceCancellationExponent V b k tb center l) ≤ K) :
    let P := pivotExpr hs e (fun i => comp (Sum.inl i))
    P.RelativeControl x K ∧ 0 < P.realEval x ∧ |Real.log (P.realEval x)-G| ≤ 1 := by
  let c := fun i => comp (Sum.inl i)
  let P := pivotExpr hs e c
  have hu : AtomSlotsCorrect slot u c := by
    intro i
    simpa only [internalSlot,Sum.elim_inl,c] using hc (Sum.inl i)
  have hsplit := atomSlots_reorder slot (History.supported_small_split hs) e.small he
  have hl := atomSlots_leftPart slot _ hsplit
  have hr := atomSlots_rightPart slot _ hsplit
  have hlc := atomSlots_positive_cells slot center x hx hsource hp _ hl
  have hrc := atomSlots_positive_cells slot center x hx hsource hm _ hr
  have huc := atomSlots_positive_cells slot center x hx hsource u c hu
  have huf : ∀ i, |Real.log ((c i).realEval x)-center (u.get i).origin| ≤ 1 := by
    intro i
    apply huc.2 i
    have hh := History.supported_compensation_roles hs (u.get i) (List.get_mem u i)
    simp only [hh,ne_eq,reduceCtorEq,not_false_eq_true]
  have hcell : giantCell G (P.realEval x) ≠ 0 := by
    intro hz
    apply hsupport
    simp only [encode,realHistorySupportWeight,treeRoot_encode,leftState]
    change giantCell G (P.realEval x) * _ * _ = 0
    rw [hz,zero_mul,zero_mul]
  obtain ⟨hP,hPG⟩ := giantCell_ne_zero_support G (P.realEval x) hcell
  have hb := leafBins_of_supportWeight_ne_zero b s k tb td G outside x
    (History.node a p u hp hm left right) (encode V outside _ hs e comp)
    hlabels.leaves hsupport
  have hleft := left_inherited_window b s k tb td G center x hs e comp hb
    hlabels.2.1 hplus hlc.1 hgp hlc.2
  have hright := right_inherited_window b s k tb td G center x hs e comp hb
    hlabels.2.2.1 hminus hrc.1 hgm hrc.2
  have hremoved := removed_window b k center x hs c hlabels.2.2.2.1 huc.1 huf
  refine ⟨?_,hP,hPG⟩
  apply pivot_relativeControl_of_source_windows b k tb G K center x hs e c hx
    (fun i => by obtain ⟨j,hj,_⟩ := he i; exact ⟨j,hj⟩)
    (fun i => by obtain ⟨j,hj,_⟩ := hu i; exact ⟨j,hj⟩) her hplus hminus hP
    (by linarith [(abs_le.mp hPG).1])
    (by linarith [(abs_le.mp hleft).2])
    (by linarith [(abs_le.mp hright).2])
    (by linarith [(abs_le.mp hremoved).1]) hK

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
