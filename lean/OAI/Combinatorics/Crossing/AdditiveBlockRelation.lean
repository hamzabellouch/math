import OAI.Combinatorics.Crossing.CyclePairing
import OAI.Combinatorics.Crossing.FourCyclePairing

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

theorem fourCycle_pairing_zero (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (i k i₀ : Fin m) (p p' q q' : Fin n) :
    edgePairing C.cycleIntersectionMatrix (walkEdgeChain (fourCycleWalk i i₀ p p'))
      (walkEdgeChain (fourCycleWalk k i₀ q q'))=0 := by
  by_cases hi : i=i₀
  · subst i
    have hz : walkEdgeChain (fourCycleWalk i₀ i₀ p p')=0 := by rw [fourCycleWalk_chain]; abel
    rw [hz]
    simp [edgePairing]
  by_cases hk : k=i₀
  · subst k
    have hz : walkEdgeChain (fourCycleWalk i₀ i₀ q q')=0 := by rw [fourCycleWalk_chain]; abel
    rw [hz]
    simp [edgePairing]
  by_cases hp : p=p'
  · subst p'
    have hz : walkEdgeChain (fourCycleWalk i i₀ p p)=0 := by rw [fourCycleWalk_chain]; abel
    rw [hz]
    simp [edgePairing]
  by_cases hq : q=q'
  · subst q'
    have hz : walkEdgeChain (fourCycleWalk k i₀ q q)=0 := by rw [fourCycleWalk_chain]; abel
    rw [hz]
    simp [edgePairing]
  exact C.lemma3_1 hnorm hstraight htrans _ _
    (fourCycleWalk_isCycle i i₀ p p' hi hp) (fourCycleWalk_isCycle k i₀ q q' hk hq)

theorem lemma3_2 (hnorm : NoAdjacentCrossings D)
    (hstraight : LocallyStraightCrossings D) (htrans : LocallyTransverseCrossings D)
    (i k i₀ : Fin m) :
    ∃ r c : Fin n → ℝ, ∀ p q,
      blockRectangle C.cycleIntersectionMatrix i k i₀ p q=r p+c q := by
  cases n with
  | zero => exact ⟨0,0,fun p => Fin.elim0 p⟩
  | succ n =>
    apply rectangle_additive (blockRectangle C.cycleIntersectionMatrix i k i₀) 0 0
    intro p p' q q'
    rw [← fourCycle_pairing_rectangle]
    exact C.fourCycle_pairing_zero hnorm hstraight htrans i k i₀ p p' q q'

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
