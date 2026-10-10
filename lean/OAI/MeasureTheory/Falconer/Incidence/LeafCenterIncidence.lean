import OAI.MeasureTheory.Falconer.Estimates.QuarterEndpointMap
import OAI.MeasureTheory.Falconer.Incidence.QuarterPencilGeometry

namespace OAI

/-! Original incidences survive moving points to their assigned leaf centers.
The half-slope chart leaves a fixed margin in the terminal tube width. -/
namespace Falconer
open Set Regularization

theorem cube_center_incident {δ : ℝ} (hδ : 0 ≤ δ) (Q : DyadicCube 2)
    {x l : Space 2} (hx : x ∈ Q.carrier) (hl : |l 0| ≤ 1/2)
    (hi : TubeIncident δ x l) (hsmall : 16*δ ≤ Q.side) :
    TubeIncident Q.side Q.center l := by
  have hside : 0 ≤ Q.side := (by positivity : 0 ≤ 16*δ).trans hsmall
  have h0 := Q.center_coordinate_bound hx 0
  have h1 := Q.center_coordinate_bound hx 1
  have hres := tube_residual_le hδ (hl.trans (by norm_num)) hi
  have hm : |l 0*(x 0-Q.center 0)| ≤ Q.side/4 := by
    rw [abs_mul]
    calc
      _ ≤ (1/2)*(Q.side/2) := mul_le_mul hl h0 (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hres' : |Q.center 1-l 0*Q.center 0-l 1| ≤ Q.side := by
    calc
      _ = |(x 1-l 0*x 0-l 1)+(Q.center 1-x 1)+l 0*(x 0-Q.center 0)| := by congr 1; ring
      _ ≤ |(x 1-l 0*x 0-l 1)+(Q.center 1-x 1)|+|l 0*(x 0-Q.center 0)| := abs_add_le _ _
      _ ≤ (|x 1-l 0*x 0-l 1|+|Q.center 1-x 1|)+|l 0*(x 0-Q.center 0)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 2*δ+Q.side/2+Q.side/4 := by rw [abs_sub_comm (Q.center 1)]; gcongr
      _ ≤ _ := by linarith
  have hden : 0 < Real.sqrt (1+(l 0)^2) := Real.sqrt_pos.mpr (by positivity)
  have hden1 : 1 ≤ Real.sqrt (1+(l 0)^2) := by
    exact (Real.one_le_sqrt).mpr (by nlinarith only [sq_nonneg (l 0)])
  apply (div_le_iff₀ hden).2
  exact hres'.trans (le_mul_of_one_le_right hside hden1)

theorem root_leaf_quarter_incident {N : ℕ} (Q : DyadicCube 2) (hQ : Q.side = 1)
    {r : CellPath 2} (hr : r ∈ cubePaths 2 N) {δ : ℝ} (hδ : 0 ≤ δ)
    {x l : Space 2} (hx : x ∈ (Q.descendant r).carrier) (hl : |l 0| ≤ 1/2)
    (hi : TubeIncident δ x l) (hsmall : 16*δ ≤ 1/(2:ℝ)^N) :
    TubeIncident (1/(2:ℝ)^(N+2)) (quarterEndpointPoint Q 0 [] r)
      (localCellLine 4 (Q.center 0) (Q.center 1) l) := by
  have hside : (Q.descendant r).side = 1/(2:ℝ)^N := by
    rw [Q.descendant_side,(mem_cubePaths _ _ _).mp hr,hQ]
  have hc := cube_center_incident hδ (Q.descendant r) hx hl hi (hside.symm ▸ hsmall)
  have hh := localCellLine_incident (by norm_num : (0:ℝ) < 4)
    (Q.center 0) (Q.center 1) (Q.descendant r).center l hc
  have hwidth : (Q.descendant r).side/4 = 1/(2:ℝ)^(N+2) := by
    rw [hside,pow_add]
    norm_num
    ring
  rw [hwidth] at hh
  simpa only [quarterEndpointPoint,pow_zero,div_one,DyadicCube.descendant] using hh

end Falconer

end OAI
