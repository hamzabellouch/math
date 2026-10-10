import OAI.Combinatorics.Crossing.OddNormalizedLowerBound
import OAI.Combinatorics.Crossing.ExpectedTrackGeometry

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem odd_crossing_lower_bound (m s : ℕ) (D : AdmissibleDrawing m (2*s+1)) :
    axisPairs m*axisPairs (2*s+1) ≤ crossingCount D := by
  by_cases hm : 0 < m
  · by_cases hs : 0 < s
    · obtain ⟨A,hcount,hpoly,hnorm,hstraight,htrans⟩ := polygonal_no_adjacent_locally_transverse D
      obtain ⟨V⟩ := nonempty_vertexTruncation A.toContinuousDrawing hpoly
      obtain ⟨C⟩ := nonempty_truncatedSpokeCoordinates V hnorm
      rw [axisPairs_odd]
      exact (C.odd_normalized_crossing_lower_bound hnorm hstraight htrans s hs rfl hm).trans hcount
    · have he : s=0 := Nat.eq_zero_of_not_pos hs
      subst s
      simp [axisPairs]
  · have he : m=0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp [axisPairs]

end Zarankiewicz

end

end OAI
