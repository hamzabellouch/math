import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.CleanSupportPartition
import OAI.Analysis.RieszRectifiability.Packing.EuclideanPackingBound

namespace OAI

/-!
# Finite cell centers near a surface ball

Compactness makes the separated lattice centers near a ball finite. A Euclidean packing
estimate bounds their number uniformly in the ball center and radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem surface_ball_cell_centers_finite {d : ℕ} (ν : Measure (Ambient d))
    (r : ℝ) (hr : 0 < r) (a : Ambient d) :
    {z : (supportLatticeNets ν r hr 0).points | dist (z : Ambient d) a ≤ 5 * r}.Finite := by
  have hf := separated_set_finite_inter_compact (supportLatticeNets ν r hr 0).points
    (closedBall a (5 * r)) (latticeRadius r 0) (latticeRadius_pos r hr 0)
    (supportLatticeNets ν r hr 0).separated (isCompact_closedBall _ _)
  have hpre := hf.preimage (f := fun z : (supportLatticeNets ν r hr 0).points => (z : Ambient d))
    Subtype.val_injective.injOn
  apply hpre.subset
  intro z hz
  exact ⟨z.property, hz⟩

def surfaceBallCellCenters {d : ℕ} (ν : Measure (Ambient d))
    (r : ℝ) (hr : 0 < r) (a : Ambient d) : Finset (supportLatticeNets ν r hr 0).points :=
  (surface_ball_cell_centers_finite ν r hr a).toFinset

theorem mem_surfaceBallCellCenters {d : ℕ} (ν : Measure (Ambient d))
    (r : ℝ) (hr : 0 < r) (a : Ambient d) (z : (supportLatticeNets ν r hr 0).points) :
    z ∈ surfaceBallCellCenters ν r hr a ↔ dist (z : Ambient d) a ≤ 5 * r := by
  simp only [surfaceBallCellCenters, Set.Finite.mem_toFinset, mem_ofPred_eq]

theorem surfaceBallCellCenters_card_le {d : ℕ} (ν : Measure (Ambient d))
    (r : ℝ) (hr : 0 < r) (a : Ambient d) :
    (surfaceBallCellCenters ν r hr a).card ≤ 11 ^ d := by
  classical
  let F := surfaceBallCellCenters ν r hr a
  let f : (supportLatticeNets ν r hr 0).points → Ambient d := fun z => z.val - a
  have hinj : Set.InjOn f F := by
    intro z hz w hw heq
    apply Subtype.ext
    have h := congrArg (fun v : Ambient d => v + a) heq
    simpa only [f, sub_add_cancel] using! h
  have hbound : ∀ x ∈ F.image f, ‖x‖ ≤ 5 * r := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    simpa only [f, ← dist_eq_norm] using! (mem_surfaceBallCellCenters ν r hr a z).mp hz
  have hsep : ∀ x ∈ F.image f, ∀ y ∈ F.image f, x ≠ y → 2 * (r / 2) ≤ dist x y := by
    intro x hx y hy hxy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    have hzw : (z : Ambient d) ≠ (w : Ambient d) := fun h => hxy (congrArg (fun v => v - a) h)
    have h := (supportLatticeNets ν r hr 0).separated z.property w.property hzw
    simpa only [f, dist_sub_right, latticeRadius_zero,
      mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using! h
  have hcard := euclidean_separated_card_le (F.image f) (5 * r) (r / 2)
    (by positivity) (by positivity) hbound hsep
  have heq : (5 * r + r / 2) / (r / 2) = 11 := by
    apply (div_eq_iff (show r / 2 ≠ 0 by positivity)).mpr
    ring
  rw [Finset.card_image_iff.mpr hinj, heq] at hcard
  exact_mod_cast hcard

theorem surface_ball_covered_by_selected_cells_off_exceptional {d : ℕ}
    (ν : Measure (Ambient d)) (r : ℝ) (hr : 0 < r) (a : Ambient d)
    (x : Ambient d) (hx : x ∈ ν.support ∩ closedBall a (3 * r))
    (hnot : x ∉ supportLatticeExceptional ν r hr) :
    ∃ z ∈ surfaceBallCellCenters ν r hr a, x ∈ cleanSupportCell ν r hr 0 z := by
  obtain ⟨z, hz⟩ := cleanSupportCell_cover ν r hr 0 x hx.1 hnot
  refine ⟨z, (mem_surfaceBallCellCenters ν r hr a z).mpr ?_, hz⟩
  have hnear := (supportLatticeCell_bounds ν r hr 0 z).2 hz.1
  simp only [latticeRadius_zero] at hnear
  have hnear' : dist (z : Ambient d) x ≤ 2 * r := by simpa only [mem_closedBall, dist_comm] using! hnear
  have ha : dist x a ≤ 3 * r := hx.2
  exact (dist_triangle _ x a).trans (by linarith)

theorem selected_surface_ball_cell_subset_seven_ball {d : ℕ}
    (ν : Measure (Ambient d)) (r : ℝ) (hr : 0 < r) (a : Ambient d)
    (z : (supportLatticeNets ν r hr 0).points) (hz : z ∈ surfaceBallCellCenters ν r hr a) :
    cleanSupportCell ν r hr 0 z ⊆ closedBall a (7 * r) := by
  intro x hx
  have hnear := (supportLatticeCell_bounds ν r hr 0 z).2 hx.1
  simp only [latticeRadius_zero] at hnear
  have hxz : dist x (z : Ambient d) ≤ 2 * r := hnear
  have hza := (mem_surfaceBallCellCenters ν r hr a z).mp hz
  change dist x a ≤ 7 * r
  exact (dist_triangle x (z : Ambient d) a).trans (by linarith)

end

end RieszRectifiability

end OAI
