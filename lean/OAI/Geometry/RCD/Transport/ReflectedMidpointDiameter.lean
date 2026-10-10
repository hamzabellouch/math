import OAI.Geometry.RCD.Transport.PointedMidpointSets

namespace OAI

/-! # The elementary diameter bound in the isodiametric argument -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

/-- Midpoints of a set and its reflection lie in the ball whose radius
is half the original diameter. -/
theorem reflected_midpoints_subset_closedBall {n : ℕ} {A : Set (Euclidean n)}
    (hA : Bornology.IsBounded A) :
    midpointSet A (Neg.neg '' A) ⊆ closedBall 0 (diam A/2) := by
  rintro x ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
  obtain ⟨c,hc,rfl⟩ := hb
  rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have hd := dist_le_diam_of_mem hA ha hc
  rw [dist_eq_norm] at hd
  rw [sub_eq_add_neg] at hd
  linarith only [hd]

end RegularPointCoordinates

end

end OAI
