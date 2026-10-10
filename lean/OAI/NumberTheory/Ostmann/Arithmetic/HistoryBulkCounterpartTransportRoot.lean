import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCounterpartTransportBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkCounterpartTransport
open Construction Construction.CanonicalOccurrenceTransport HistoryOccurrenceVariables
open HistoryGiantReferenceCounterpart HistoryPairBulkTransport

theorem redrawRootSmall_eq_assigned {l : ℕ} (h : History l)
    (sources : SourceFamily) (T : List SourceSlot)
    (x₀ x : SourceAssignment sources T)
    (hr : h.root.small = assignedSlots sources T x₀)
    (hlen : h.root.small.length = T.length) :
    redrawRootSmall h (fun i => (x (Fin.cast hlen i)).val) = assignedSlots sources T x := by
  unfold redrawRootSmall
  rw [List.ofFn_congr hlen]
  unfold assignedSlots Template.sample
  apply congrArg List.ofFn
  funext i
  have hi : h.root.small.get (Fin.cast hlen.symm i) =
      ({role := T[i].role, value := (x₀ i).val, origin := T[i].origin} : SmallSlot) := by
    simp only [List.get_eq_getElem]
    simp only [hr, assignedSlots, Template.sample, List.getElem_ofFn]
    rfl
  rw [hi]
  rfl

theorem diagonalRootCounterpart_assigned
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
    (s : ℤ) (gp gm : ℕ)
    (x₀ x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l)
    (F : Key (assignedHistory sources seed V l s gp gm x₀ c) → ℝ)
    (Q : ℝ) (hQ : F (.inl true) = Q)
    (hx : ∀ i : Fin (Template.current seed l).length,
      F (decodedCoordinateEquiv sources seed V l
        (assignedRoot sources (Template.current seed l) s gp gm x₀) c
        (assignedRoot_matches sources (Template.current seed l) s gp gm x₀) (.inr (.inl i))) =
          ((x i).val : ℝ))
    (j : ℕ) (A B G : ℝ) (center : ℕ → ℝ) :
    diagonalRootCounterpart (assignedHistory sources seed V l s gp gm x₀ c) j A B G center F =
      remainingCounterpartAt sources (Template.current seed l) j A B G center
        (restoringAssignmentEquiv sources j (Template.current seed l) x).1
        (restoringAssignmentEquiv sources j (Template.current seed l) x).2 Q := by
  let h := assignedHistory sources seed V l s gp gm x₀ c
  have hr : h.root.small = assignedSlots sources (Template.current seed l) x₀ := by
    simp only [h, assignedHistory, decodeHistory_root, assignedRoot]
  have hlen : h.root.small.length = (Template.current seed l).length := by
    rw [hr, assignedSlots_length]
  let values : Fin h.root.small.length → ℕ := fun i => (x (Fin.cast hlen i)).val
  have hF : ∀ i, F (.inr (.inl i)) = (values i : ℝ) := by
    intro i
    have he := hx (Fin.cast hlen i)
    have hkey : decodedCoordinateEquiv sources seed V l
        (assignedRoot sources (Template.current seed l) s gp gm x₀) c
        (assignedRoot_matches sources (Template.current seed l) s gp gm x₀)
        (.inr (.inl (Fin.cast hlen i))) = .inr (.inl i) := rfl
    rw [hkey] at he
    exact he
  apply diagonalRootCounterpart_redraw h values F hF Q hQ sources (Template.current seed l) j
    (restoringAssignmentEquiv sources j (Template.current seed l) x).1
    (restoringAssignmentEquiv sources j (Template.current seed l) x).2 _ A B G center
  exact (redrawRootSmall_eq_assigned h sources (Template.current seed l) x₀ x hr hlen).trans
    (assignedSlots_split_reinsert sources j (Template.current seed l) x)

end Ostmann.Arithmetic.HistoryBulkCounterpartTransport

end

end OAI
