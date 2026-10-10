import OAI.Analysis.LipschitzHilbert.Trees.BoundaryDistanceAverage

namespace OAI

/-! One uniform translation modulo the root width induces the correct
boundary-distance average at every level of the nested angular grid. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.AngularGrid

def withOrigin (g : AngularGrid) (origin : ℝ) : AngularGrid := {g with origin := origin}

@[simp] theorem width_withOrigin (g : AngularGrid) (origin : ℝ) (i : ℕ) :
    (g.withOrigin origin).width i = g.width i := rfl

theorem normalized_boundaryDistance_withOrigin (g : AngularGrid) (i : ℕ) (s origin : ℝ) :
    (g.withOrigin origin).boundaryDistance i s/g.width i =
      unitBoundaryDistance ((s-origin)/g.width i) := by
  rw [boundaryDistance_eq_unit,width_withOrigin]
  change (g.width i*unitBoundaryDistance ((s-origin)/g.width i))/g.width i = _
  field_simp [(g.width_pos i).ne']

theorem common_translation_boundary_integral (g : AngularGrid) (i : ℕ) (s : ℝ)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 (1/2:ℝ)) :
    (∫ origin in (0:ℝ)..g.rootWidth,
      f ((g.withOrigin origin).boundaryDistance i s/g.width i)) =
        2*g.rootWidth*(∫ b in (0:ℝ)..(1/2:ℝ), f b) := by
  simp_rw [g.normalized_boundaryDistance_withOrigin i s,sub_div]
  rw [intervalIntegral.integral_comp_sub_div (fun u => f (unitBoundaryDistance u))
    (g.width_pos i).ne']
  simp only [zero_div,sub_zero,smul_eq_mul]
  have hG : (g.branching:ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have hcount : g.rootWidth/g.width i = ((g.branching^i:ℕ):ℝ) := by
    push_cast
    unfold width
    field_simp [g.rootWidth_pos.ne',pow_ne_zero i hG]
  rw [hcount]
  have h := unitBoundaryDistance_period_integral f hf (g.branching^i)
    (s/g.width i-((g.branching^i:ℕ):ℝ))
  rw [sub_add_cancel] at h
  rw [h]
  have hw : g.width i*((g.branching^i:ℕ):ℝ) = g.rootWidth := by
    push_cast
    unfold width
    field_simp [g.rootWidth_pos.ne',pow_ne_zero i hG]
  rw [← mul_assoc,← mul_assoc,hw]
  ring

end LipschitzHilbert.AngularGrid

end

end OAI
