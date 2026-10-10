import Mathlib
import OAI.Geometry.RecorderBoxes.Placement

namespace OAI

/-! Separated physical rectangles and their reciprocal affine maps. -/

namespace Solenoidal
namespace Bridge
variable {M : Machine}
noncomputable def sourceRectangle {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (i : Branch M) : Rectangle := physicalBox i.src (branchSource e i)

noncomputable def targetRectangle {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (i : Branch M) : Rectangle := physicalBox i.dst (branchTarget e i)

theorem common_gap_le_kappa (m : ℕ) : kappa M / Radix.base m ^ 2 ≤ kappa M := by
  apply (div_le_self (kappa_pos M).le)
  have := Radix.base_three_le m
  nlinarith

 
theorem source_rectangles_separated {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    {i j : Branch M} (hij : i ≠ j) :
    (sourceRectangle e i).SeparatedBy (kappa M / Radix.base m ^ 2) (sourceRectangle e j) := by
  by_cases hs : i.src = j.src
  · have h := Rectangle.gap_mono (branch_source_gap e hij hs) (inverse_square_le_inverse m)
    have hp := physical_gap_same i.src h
    simpa only [sourceRectangle, hs, mul_one_div] using hp
  · exact Rectangle.gap_mono
      (physical_gap_different hs (source_in_unit _ _) (source_in_unit _ _))
      (common_gap_le_kappa m)

 

theorem target_rectangles_separated {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    {i j : Branch M} (hij : i ≠ j) :
    (targetRectangle e i).SeparatedBy (kappa M / Radix.base m ^ 2) (targetRectangle e j) := by
  by_cases hs : i.dst = j.dst
  · have hp := physical_gap_same i.dst (branch_target_gap e hij hs)
    simpa only [targetRectangle, hs, mul_one_div] using hp
  · exact Rectangle.gap_mono
      (physical_gap_different hs (target_in_unit _ _ _) (target_in_unit _ _ _))
      (common_gap_le_kappa m)

 
noncomputable def affine {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (i : Branch M) (p : ℝ × ℝ) : ℝ × ℝ :=
  place i.dst (Radix.update (e i.read) (e i.written) (e i.left) i.move (unplace i.src p))

 
theorem affine_image {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M) :
    affine e i '' (sourceRectangle e i).carrier = (targetRectangle e i).carrier := by
  rw [sourceRectangle, targetRectangle, physicalBox_carrier, physicalBox_carrier]
  rw [Set.image_image]
  have he : (affine e i ∘ place i.src) =
      place i.dst ∘ Radix.update (e i.read) (e i.written) (e i.left) i.move := by
    funext p
    simp [affine]
  change (affine e i ∘ place i.src) '' (branchSource e i).carrier = _
  rw [he, Set.image_comp]
  congr 1
  exact (Radix.full_image (e i.read) (e i.written) (e i.left) i.move).trans
    (targetBox_carrier _ _ _).symm

 
theorem affine_linear_part {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M)
    (p q : ℝ × ℝ) :
    affine e i p - affine e i q =
      (Radix.scale m i.move * (p.1 - q.1), (Radix.scale m i.move)⁻¹ * (p.2 - q.2)) := by
  have hh := Radix.reciprocal_linear_part (e i.read) (e i.written) (e i.left) i.move
    (unplace i.src p) (unplace i.src q)
  apply Prod.ext
  · calc
      _ = kappa M * (Radix.update (e i.read) (e i.written) (e i.left) i.move (unplace i.src p) -
          Radix.update (e i.read) (e i.written) (e i.left) i.move (unplace i.src q)).1 := by
        dsimp [affine, place]; ring
      _ = kappa M * (Radix.scale m i.move * ((unplace i.src p).1 - (unplace i.src q).1)) := by
        rw [hh]
      _ = _ := by dsimp [unplace]; field_simp [(kappa_pos M).ne']; ring
  · calc
      _ = kappa M * (Radix.update (e i.read) (e i.written) (e i.left) i.move (unplace i.src p) -
          Radix.update (e i.read) (e i.written) (e i.left) i.move (unplace i.src q)).2 := by
        dsimp [affine, place]; ring
      _ = kappa M * ((Radix.scale m i.move)⁻¹ * ((unplace i.src p).2 - (unplace i.src q).2)) := by
        rw [hh]
      _ = _ := by dsimp [unplace]; field_simp [(kappa_pos M).ne']; ring
end Bridge
end Solenoidal

end OAI
