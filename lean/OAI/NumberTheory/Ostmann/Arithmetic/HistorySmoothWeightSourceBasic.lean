import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCutoff
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSlots

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Construction Characters.RationalHistory

theorem giantCell_ne_zero_support (G p : ℝ) (hp : giantCell G p ≠ 0) :
    0 < p ∧ |Real.log p-G| ≤ 1 := by
  have hpos : 0 < p := by
    by_contra hn
    exact hp (giantCell_of_nonpos G (le_of_not_gt hn))
  rw [giantCell_of_pos G hpos] at hp
  have hs := smoothPartition_support_subset hp
  exact ⟨hpos,abs_le.mpr ⟨hs.1.le,hs.2.le⟩⟩

namespace HistorySymbolicEncoding
open HistorySymbolicState
variable {ι : Type*}

def IndependentSourceCells (slot : ι → Option SmallSlot) (center : ℕ → ℝ) (x : ι → ℝ) : Prop :=
  ∀ j q, slot j = some q → q.role ≠ .bulk → |Real.log (x j)-center q.origin| ≤ 1

theorem StateAtomSlots.small_positive {slot : ι → Option SmallSlot} {a : State}
    (e : StateExpr a ι) (he : StateAtomSlots slot e) (x : ι → ℝ) (hx : ∀ j, 0 < x j) :
    ∀ i, 0 < (e.small i).realEval x := by
  intro i
  obtain ⟨j,hj,_⟩ := he i
  rw [hj]
  exact hx j

theorem StateAtomSlots.small_cells {slot : ι → Option SmallSlot} {a : State}
    (e : StateExpr a ι) (he : StateAtomSlots slot e) (center : ℕ → ℝ) (x : ι → ℝ)
    (hx : IndependentSourceCells slot center x) :
    ∀ i, (a.small.get i).role ≠ .bulk →
      |Real.log ((e.small i).realEval x)-center (a.small.get i).origin| ≤ 1 := by
  intro i hi
  obtain ⟨j,hj,hslot⟩ := he i
  rw [hj]
  exact hx j (a.small.get i) hslot hi

theorem logCurve_exp [DecidableEq ι] (y : ι → ℝ) (i : ι) (t : ℝ) :
    Expr.logCurve (fun j => Real.exp (y j)) i t =
      (fun j => Real.exp (y j + if j=i then t else 0)) := by
  funext j
  exact (Real.exp_add _ _).symm

end HistorySymbolicEncoding
end Ostmann.Arithmetic

end

end OAI
