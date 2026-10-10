import OAI.MeasureTheory.Falconer.Recursion.ParentConeGeometry
import OAI.MeasureTheory.Falconer.Geometry.DyadicPacking

namespace OAI

namespace PlanarFalconer
open Set Metric

noncomputable def rootPatchEnvelope (x : Plane) (r : ℝ) : DyadicSquare :=
  ⟨x 0-2*r,x 1-2*r,4*r⟩

theorem rootPatchEnvelope_center (x : Plane) (r : ℝ) : (rootPatchEnvelope x r).center = x := by
  ext i
  fin_cases i <;> simp [rootPatchEnvelope,DyadicSquare.center] <;> ring

theorem closedBall_subset_rootPatchEnvelope (x : Plane) {r : ℝ} (hr : 0 < r) :
    closedBall x r ⊆ (rootPatchEnvelope x r).carrier := by
  intro z hz
  have h₀ := abs_le.mp ((plane_coordinate_dist_le z x 0).trans hz)
  have h₁ := abs_le.mp ((plane_coordinate_dist_le z x 1).trans hz)
  change x 0-2*r ≤ z 0 ∧ z 0 < x 0-2*r+4*r ∧ x 1-2*r ≤ z 1 ∧ z 1 < x 1-2*r+4*r
  exact ⟨by linarith only [h₀.1, hr], by linarith only [h₀.2, hr],
    by linarith only [h₁.1, hr], by linarith only [h₁.2, hr]⟩

theorem rootPatchEnvelopes_separated (x y : Plane) (hxy : x ≠ y) :
    let r := dist x y/1000
    let U := rootPatchEnvelope x r
    let V := rootPatchEnvelope y r
    0 < U.side ∧ 0 < V.side ∧ U.side ≤ 4*r ∧ V.side ≤ 4*r ∧
      100*(4*r) ≤ dist U.center V.center := by
  have hdist := dist_pos.mpr hxy
  dsimp only
  rw [rootPatchEnvelope_center,rootPatchEnvelope_center]
  dsimp [rootPatchEnvelope]
  exact ⟨by positivity,by positivity,le_rfl,le_rfl,by linarith only [hdist]⟩

theorem rootPatchEnvelopes_distance (x y : Plane) (hxy : x ≠ y)
    {u v : Plane} (hu : u ∈ (rootPatchEnvelope x (dist x y/1000)).carrier)
    (hv : v ∈ (rootPatchEnvelope y (dist x y/1000)).carrier) :
    dist x y/2 ≤ dist u v ∧ dist u v ≤ 2*dist x y := by
  have hdist := dist_pos.mpr hxy
  have h₁ := (rootPatchEnvelope x (dist x y/1000)).dist_center_le_three_quarters (by
    dsimp [rootPatchEnvelope]; positivity) hu
  have h₂ := (rootPatchEnvelope y (dist x y/1000)).dist_center_le_three_quarters (by
    dsimp [rootPatchEnvelope]; positivity) hv
  rw [rootPatchEnvelope_center] at h₁ h₂
  dsimp [rootPatchEnvelope] at h₁ h₂
  have h₃ := dist_triangle4 u x y v
  have h₄ := dist_triangle4 x u v y
  rw [dist_comm y v] at h₃
  rw [dist_comm x u] at h₄
  constructor
  · linarith only [h₁, h₂, h₄, hdist]
  · linarith only [h₁, h₂, h₃, hdist]

end PlanarFalconer

end OAI
