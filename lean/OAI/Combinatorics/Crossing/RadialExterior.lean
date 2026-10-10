import OAI.Combinatorics.Crossing.ParallelDirection
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem squaredLength_add_smul (u v : Plane) (t : ℝ) :
    squaredLength (u+t • v)=squaredLength u+2*t*dot2 u v+t^2*squaredLength v := by
  dsimp [squaredLength,dot2]
  ring

theorem squaredLength_segment_translated (a b z : Plane) (t : ℝ) :
    squaredLength (segmentPoint a b t-z)=
      squaredLength (a-z)+2*t*dot2 (a-z) (b-a)+t^2*squaredLength (b-a) := by
  dsimp [squaredLength,dot2,segmentPoint]
  ring

theorem exterior_segment_of_dot (z a b : Plane) (r : ℝ)
    (ha : r^2 < squaredLength (a-z)) (hd : 0 ≤ dot2 (a-z) (b-a)) :
    segment ℝ a b ⊆ {x | r^2 < squaredLength (x-z)} := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,rfl⟩ := hx
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  change r^2 < squaredLength (segmentPoint a b t.val-z)
  rw [squaredLength_segment_translated]
  have h₁ : 0 ≤ 2*t.val*dot2 (a-z) (b-a) := mul_nonneg (mul_nonneg (by norm_num) t.property.1) hd
  have h₂ : 0 ≤ t.val^2*squaredLength (b-a) := by dsimp [squaredLength]; positivity
  linarith

theorem radial_spur_exterior (z x : Plane) (r α : ℝ)
    (hx : squaredLength (x-z)=r^2) (hr : 0 < r) (hα : 0 < α) :
    segment ℝ x (x+α • (x-z)) ⊆ insert x {y | r^2 < squaredLength (y-z)} := by
  intro y hy
  rw [← Path.range_segment] at hy
  obtain ⟨t,rfl⟩ := hy
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  by_cases ht : t.val=0
  · left
    change segmentPoint x (x+α • (x-z)) t.val=x
    rw [ht,segmentPoint_zero]
  · right
    have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    change r^2 < squaredLength (segmentPoint x (x+α • (x-z)) t.val-z)
    have he : squaredLength (segmentPoint x (x+α • (x-z)) t.val-z)=
        (1+t.val*α)^2*squaredLength (x-z) := by
      dsimp [squaredLength,segmentPoint]
      ring
    rw [he,hx]
    have hp := mul_pos htpos hα
    nlinarith [sq_pos_of_pos hr,mul_pos hp (sq_pos_of_pos hr)]

theorem radial_tip_dot (z x : Plane) (α : ℝ) :
    dot2 (x-z) ((x+α • (x-z))-x)=α*squaredLength (x-z) := by
  dsimp [dot2,squaredLength]
  ring

end Zarankiewicz

end

end OAI
