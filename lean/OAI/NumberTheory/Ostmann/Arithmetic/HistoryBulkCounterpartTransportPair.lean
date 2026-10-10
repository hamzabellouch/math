import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCounterpartTransportRoot
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedSample

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkCounterpartTransport
open Construction Construction.CanonicalOccurrenceTransport
open HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryGiantReferenceCounterpart HistoryPairBulkTransport
variable (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
variable (s : ℤ) (gp gm : ℕ)
variable (x₀ x : SourceAssignment sources (Template.current seed l))
variable (c : HistoryChoices sources seed V l) (h : History l)
variable (F : PairKey h (assignedHistory sources seed V l s gp gm x₀ c) → ℝ) (Q : ℝ)
variable (hQ : F (rightMap h (assignedHistory sources seed V l s gp gm x₀ c) (.inl true)) = Q)
variable (hx : ∀ i : Fin (Template.current seed l).length,
  F (rightMap h (assignedHistory sources seed V l s gp gm x₀ c) (decodedCoordinateEquiv sources seed V l
    (assignedRoot sources (Template.current seed l) s gp gm x₀) c
    (assignedRoot_matches sources (Template.current seed l) s gp gm x₀) (.inr (.inl i)))) =
      ((x i).val : ℝ))

include hQ hx

theorem pairedRootCounterpart_assigned (j : ℕ) (A B G : ℝ) (center : ℕ → ℝ) :
    pairedRootCounterpart h (assignedHistory sources seed V l s gp gm x₀ c) j A B G center F =
      remainingCounterpartAt sources (Template.current seed l) j A B G center
        (restoringAssignmentEquiv sources j (Template.current seed l) x).1
        (restoringAssignmentEquiv sources j (Template.current seed l) x).2 Q := by
  rw [pairedRootCounterpart_pullback]
  exact diagonalRootCounterpart_assigned sources seed V l s gp gm x₀ x c
    (F ∘ rightMap h (assignedHistory sources seed V l s gp gm x₀ c)) Q hQ hx j A B G center

theorem new_counterpart_mul_pairedRealXi {outside : List ℕ}
    (hs : h.Supported V outside) (ks : (assignedHistory sources seed V l s gp gm x₀ c).Supported V outside)
    (j b sc : ℕ) (A B X tb td G : ℝ) (center : ℕ → ℝ) :
    (remainingCounterpartAt sources (Template.current seed l) j A B G center
      (restoringAssignmentEquiv sources j (Template.current seed l) x).1
      (restoringAssignmentEquiv sources j (Template.current seed l) x).2 Q : ℂ) *
        pairedRealXi b sc X tb td G h (assignedHistory sources seed V l s gp gm x₀ c) hs ks F =
      correctedPairedRealXi b sc X tb td G h (assignedHistory sources seed V l s gp gm x₀ c) hs ks A B
        (pairedDiagonalHKeys h (assignedHistory sources seed V l s gp gm x₀ c) j) (pairedDiagonalUKeys h (assignedHistory sources seed V l s gp gm x₀ c) j)
        (Finset.univ : Finset (Fin (diagonalCellKeys (assignedHistory sources seed V l s gp gm x₀ c) j).length))
        (pairedDiagonalCellCenter (assignedHistory sources seed V l s gp gm x₀ c) j G center) (pairedDiagonalCellKey h (assignedHistory sources seed V l s gp gm x₀ c) j) F := by
  change _ = (pairedRootCounterpart h (assignedHistory sources seed V l s gp gm x₀ c) j A B G center F : ℂ) *
    pairedRealXi b sc X tb td G h (assignedHistory sources seed V l s gp gm x₀ c) hs ks F
  rw [pairedRootCounterpart_assigned sources seed V l s gp gm x₀ x c h F Q hQ hx]

end Ostmann.Arithmetic.HistoryBulkCounterpartTransport

end

end OAI
