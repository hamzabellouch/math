import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryGeometry
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

/-! The normalized distance to the nearest boundary is a one-periodic
folded fractional part of the common grid translation. -/

noncomputable section
namespace LipschitzHilbert

def unitBoundaryDistance (u : ℝ) : ℝ := min (Int.fract u) (1-Int.fract u)

theorem unitBoundaryDistance_periodic : Function.Periodic unitBoundaryDistance 1 := by
  intro u
  simp only [unitBoundaryDistance,Int.fract_add_one]

theorem unitBoundaryDistance_neg (u : ℝ) : unitBoundaryDistance (-u) = unitBoundaryDistance u := by
  by_cases hu : Int.fract u = 0
  · have hneg := (Int.fract_neg_eq_zero).mpr hu
    simp only [unitBoundaryDistance,hu,hneg]
  · rw [unitBoundaryDistance,Int.fract_neg hu,unitBoundaryDistance]
    have heq : 1-(1-Int.fract u) = Int.fract u := by ring
    rw [heq,min_comm]

theorem unitBoundaryDistance_on_unit {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    unitBoundaryDistance u = min u (1-u) := by
  by_cases hu : u = 1
  · subst u
    norm_num [unitBoundaryDistance]
  · rw [unitBoundaryDistance,Int.fract_eq_self.mpr ⟨hu0,lt_of_le_of_ne hu1 hu⟩]

theorem unitBoundaryDistance_lower {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1/2) :
    unitBoundaryDistance u = u := by
  rw [unitBoundaryDistance_on_unit hu0 (by linarith),min_eq_left (by linarith)]

theorem unitBoundaryDistance_upper {u : ℝ} (hu : 1/2 ≤ u) (hu1 : u ≤ 1) :
    unitBoundaryDistance u = 1-u := by
  rw [unitBoundaryDistance_on_unit (by linarith) hu1,min_eq_right (by linarith)]

theorem unitBoundaryDistance_measurable : Measurable unitBoundaryDistance :=
  measurable_fract.min (measurable_const.sub measurable_fract)

namespace AngularGrid

theorem boundaryDistance_eq_unit (g : AngularGrid) (i : ℕ) (s : ℝ) :
    g.boundaryDistance i s = g.width i*unitBoundaryDistance ((s-g.origin)/g.width i) := by
  have hG : (g.branching:ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have hi : g.index i s = ⌊(s-g.origin)/g.width i⌋ := by
    unfold index width
    congr 1
    field_simp
  have hleft : s-g.left i (g.index i s) = g.width i*Int.fract ((s-g.origin)/g.width i) := by
    rw [hi,left,Int.fract]
    field_simp [(g.width_pos i).ne']
    ring
  have hright : g.left i (g.index i s)+g.width i-s =
      g.width i*(1-Int.fract ((s-g.origin)/g.width i)) := by
    calc
      _ = g.width i-(s-g.left i (g.index i s)) := by ring
      _ = g.width i-g.width i*Int.fract ((s-g.origin)/g.width i) := by rw [hleft]
      _ = _ := by ring
  rw [boundaryDistance,hleft,hright,unitBoundaryDistance,mul_min_of_nonneg _ _ (g.width_pos i).le]

end AngularGrid
end LipschitzHilbert

end

end OAI
