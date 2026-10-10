import OAI.Combinatorics.YoungDiagram.CapacityFloor

namespace OAI

/- The band criterion with real floors in both orientations of a Young diagram. -/
namespace ArithmeticTensorSquares.Capacity
open scoped BigOperators

def RealFloorBandTest (height width : Nat → Nat) (M r : Nat) : Prop :=
  ∃ d q : Nat, 1 ≤ d ∧ d ≤ 4 ∧ q ≤ 8 ∧
    2*M-1 ≤ ∑ i ∈ Finset.range d, width i ∧
    d*q+7+d ≤ 2*M-1 ∧ (r : Int) ≤
      ∑ i ∈ Finset.range q, max 0 (Int.floor (((height i : ℝ)-(d : ℝ))/2))

lemma literalBandTest_realFloor_iff (height width : Nat → Nat) (M r : Nat) :
    LiteralBandTest height width M r ↔ RealFloorBandTest height width M r := by
  simp only [LiteralBandTest, RealFloorBandTest, literalAttachmentCapacity,
    integer_division_is_floor]

theorem capacity_large_real_floor (n : Nat) (μ : YoungDiagram) (hcard : μ.card = n)
    (hM : 22 ≤ UniversalTensorSquares.largestIndex n)
    (hr : 0 < UniversalTensorSquares.remainderPairs n)
    (hcols : 2*UniversalTensorSquares.largestIndex n-1 ≤ colPrefix μ 4)
    (hrows : 2*UniversalTensorSquares.largestIndex n-1 ≤ rowPrefix μ 4) :
    RealFloorBandTest μ.colLen μ.rowLen
      (UniversalTensorSquares.largestIndex n) (UniversalTensorSquares.remainderPairs n) ∨
    RealFloorBandTest μ.rowLen μ.colLen
      (UniversalTensorSquares.largestIndex n) (UniversalTensorSquares.remainderPairs n) := by
  rcases capacity_large n μ hcard hM hr hcols hrows with h | h
  · exact Or.inl ((literalBandTest_realFloor_iff _ _ _ _).mp h)
  · exact Or.inr ((literalBandTest_realFloor_iff _ _ _ _).mp h)
end ArithmeticTensorSquares.Capacity

end OAI
