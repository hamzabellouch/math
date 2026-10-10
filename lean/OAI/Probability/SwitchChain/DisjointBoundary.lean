import OAI.Probability.SwitchChain.DisjointReconstruct
import OAI.Probability.SwitchChain.BinaryAssignments

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

variable {V : Type*} [sectionFintypeV : Fintype V]

def leftCounts (e : Fin 4 ↪ V) (G : SimpleGraph V) (w : {w : V // Outside e w}) : Nat :=
  edgeBit G (e 0) w.val + edgeBit G (e 1) w.val

def rightCounts (e : Fin 4 ↪ V) (G : SimpleGraph V) (w : {w : V // Outside e w}) : Nat :=
  edgeBit G (e 2) w.val + edgeBit G (e 3) w.val

include sectionFintypeV in
theorem edgeBit_le_one (G : SimpleGraph V) (u v : V) : edgeBit G u v ≤ 1 := by
  have retainedsectionFintypeV := sectionFintypeV
  unfold edgeBit
  split_ifs <;> omega

theorem leftCounts_le_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (w : {w : V // Outside e w}) : leftCounts e G w ≤ 2 := by
  have h0 := edgeBit_le_one G (e 0) w.val
  have h1 := edgeBit_le_one G (e 1) w.val
  unfold leftCounts
  omega

theorem rightCounts_le_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (w : {w : V // Outside e w}) : rightCounts e G w ≤ 2 := by
  have h0 := edgeBit_le_one G (e 2) w.val
  have h1 := edgeBit_le_one G (e 3) w.val
  unfold rightCounts
  omega

def assignmentBoundary (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w}) :
    Fin 4 → {w : V // Outside e w} → Prop :=
  ![BinaryAssignments.first (leftCounts e G) U,
    BinaryAssignments.second (leftCounts e G) U,
    BinaryAssignments.first (rightCounts e G) W,
    BinaryAssignments.second (rightCounts e G) W]

theorem assignmentBoundary_matches (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    BoundaryMatches e G (assignmentBoundary e G U W) := by
  intro w
  constructor
  · exact BinaryAssignments.indicator_sum (leftCounts e G) (leftCounts_le_two e G) U hU w
  · exact BinaryAssignments.indicator_sum (rightCounts e G) (rightCounts_le_two e G) W hW w

theorem assignmentBoundary_card_zero (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 0)).card =
      (BinaryAssignments.common (leftCounts e G)).card + U.card :=
  BinaryAssignments.first_card _ _ hU

theorem assignmentBoundary_card_one (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 1)).card + U.card =
      (BinaryAssignments.common (leftCounts e G)).card +
        (BinaryAssignments.singletons (leftCounts e G)).card :=
  BinaryAssignments.second_card_add _ _ hU

theorem assignmentBoundary_card_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 2)).card =
      (BinaryAssignments.common (rightCounts e G)).card + W.card :=
  BinaryAssignments.first_card _ _ hW

theorem assignmentBoundary_card_three (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 3)).card + W.card =
      (BinaryAssignments.common (rightCounts e G)).card +
        (BinaryAssignments.singletons (rightCounts e G)).card :=
  BinaryAssignments.second_card_add _ _ hW

end Problem315.DisjointEncoding

end

end OAI
