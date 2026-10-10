import Mathlib
import OAI.Geometry.HyperbolicGroups.TriangleSquare

namespace OAI

noncomputable section

open scoped Topology unitInterval

namespace HyperbolicObstruction.TriangleSquare

lemma eq_bottom_of_zero (z : Triangle) (hz : z.val 2 = 0) :
    z = quotient (⟨z.val 1,z.property.1 1,coord_le_one z 1⟩,0) := by
  have hh := sum_coords z
  apply Subtype.ext
  rw [quotient_zero]
  apply funext; intro i; fin_cases i <;> dsimp
  all_goals first | exact hz | rfl | linarith
lemma eq_left_of_zero (z : Triangle) (hz : z.val 1 = 0) :
    z = quotient (0,⟨z.val 2,z.property.1 2,coord_le_one z 2⟩) := by
  have hh := sum_coords z
  apply Subtype.ext
  rw [quotient_left]
  apply funext; intro i; fin_cases i <;> dsimp
  all_goals first | exact hz | rfl | linarith
lemma eq_right_of_zero (z : Triangle) (hz : z.val 0 = 0) :
    z = quotient (1,⟨z.val 2,z.property.1 2,coord_le_one z 2⟩) := by
  have hh := sum_coords z
  apply Subtype.ext
  rw [quotient_right]
  apply funext; intro i; fin_cases i <;> dsimp
  all_goals first | exact hz | rfl | linarith

end HyperbolicObstruction.TriangleSquare
end

end OAI
