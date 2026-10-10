import OAI.Combinatorics.Crossing.CrossingCoordinates

namespace OAI

namespace Zarankiewicz

theorem inverseCoordinates_first_segment (a b c d o : Plane) (t s : ℝ)
    (ho : o=segmentPoint a b t) :
    crossingCoordinateInverse o (b-a) (d-c) (s-t,0)=segmentPoint a b s := by
  rw [ho]
  apply Prod.ext <;> dsimp [crossingCoordinateInverse,segmentPoint] <;> ring

theorem inverseCoordinates_second_segment (a b c d o : Plane) (t s : ℝ)
    (ho : o=segmentPoint c d t) :
    crossingCoordinateInverse o (b-a) (d-c) (0,s-t)=segmentPoint c d s := by
  rw [ho]
  apply Prod.ext <;> dsimp [crossingCoordinateInverse,segmentPoint] <;> ring

theorem crossingCoordinates_first_segment (a b c d o : Plane) (t s : ℝ)
    (hd : det2 (b-a) (d-c) ≠ 0) (ho : o=segmentPoint a b t) :
    crossingCoordinates o (b-a) (d-c) (segmentPoint a b s)=(s-t,0) := by
  rw [← inverseCoordinates_first_segment a b c d o t s ho]
  exact crossingCoordinates_right_inverse o (b-a) (d-c) hd _

theorem crossingCoordinates_second_segment (a b c d o : Plane) (t s : ℝ)
    (hd : det2 (b-a) (d-c) ≠ 0) (ho : o=segmentPoint c d t) :
    crossingCoordinates o (b-a) (d-c) (segmentPoint c d s)=(0,s-t) := by
  rw [← inverseCoordinates_second_segment a b c d o t s ho]
  exact crossingCoordinates_right_inverse o (b-a) (d-c) hd _

end Zarankiewicz

end OAI
