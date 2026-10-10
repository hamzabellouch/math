import OAI.Geometry.RCD.Sobolev.InnerBallMeasuredTests
import OAI.Geometry.RCD.Sobolev.InteriorLipschitzTestProduct

namespace OAI

/-! # A bounded continuous representative of a local Lipschitz function -/

open Set Metric
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem bounded_local_representative {n : ℕ} {R : ℝ} (hR : 0≤R)
    {g : Euclidean n → ℝ} {L : ℝ≥0} (hg : LipschitzOnWith L g (closedBall 0 R)) :
    ∃ F : Euclidean n →ᵇ ℝ, EqOn F g (closedBall 0 R) := by
  obtain ⟨F,hF,he⟩ := hg.extend_real
  let A : ℝ := |g 0|+(L:ℝ)*R
  have hA : 0≤A := add_nonneg (abs_nonneg _) (mul_nonneg L.coe_nonneg hR)
  have hFb (z : Euclidean n) (hz : z∈closedBall 0 R) : |F z|≤A := by
    have hd := hF.dist_le_mul z 0
    have hzR : ‖z‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hz
    rw [Real.dist_eq,← he (mem_closedBall_self hR),dist_zero_right] at hd
    have ht := abs_add_le (F z-g 0) (g 0)
    simp only [sub_add_cancel] at ht
    dsimp only [A]
    nlinarith [mul_le_mul_of_nonneg_left hzR L.coe_nonneg]
  let H := fun z => min (max (F z) (-A)) A
  have hH : LipschitzWith L H := (hF.max_const (-A)).min_const A
  have hHb (z : Euclidean n) : |H z|≤A := by
    apply abs_le.mpr
    exact ⟨le_min (le_max_right _ _) (by linarith),min_le_right _ _⟩
  let Hc : Euclidean n →ᵇ ℝ := ⟨⟨H,hH.continuous⟩,⟨2*A,fun x y => by
    rw [Real.dist_eq]
    calc |H x-H y| ≤ |H x|+|H y| := abs_sub _ _
         _ ≤ 2*A := by linarith [hHb x,hHb y]⟩⟩
  refine ⟨Hc,?_⟩
  intro z hz
  change min (max (F z) (-A)) A=g z
  rw [max_eq_left (abs_le.mp (hFb z hz)).1,min_eq_left (abs_le.mp (hFb z hz)).2]
  exact (he hz).symm

end RegularPointCoordinates

end

end OAI
