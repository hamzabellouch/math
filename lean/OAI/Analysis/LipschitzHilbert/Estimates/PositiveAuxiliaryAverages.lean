import OAI.Analysis.LipschitzHilbert.Geometry.PositiveRectangleAuxiliary

namespace OAI

/-! Pointwise domination of the literal line and square integrals used
by the rectangle selection argument. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid

theorem positiveHorizontal_interval (f : ℝ × ℝ → ℝ≥0∞) (c r : ℝ) (hr : 0 < r)
    (z : ℝ × ℝ) (hz : z.1 ∈ Icc (c-r) (c+r)) :
    (∫⁻ x in Icc (c-r) (c+r), f (x,z.2)) ≤
      6 * ENNReal.ofReal (2*r) * positiveHorizontal f z := by
  obtain ⟨q,hq,k,j,hsub,hscale⟩ := exists_comparable_three_grid_cover c r hr
  let Q : GridChoice := ⟨q,hq⟩
  have hv0 : volume (cell q k j) ≠ 0 := by
    rw [cell_volume]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (scale_pos k))
  have hvtop : volume (cell q k j) ≠ ∞ := by rw [cell_volume]; exact ENNReal.ofReal_ne_top
  have hm : (∫⁻ x in cell q k j, f (x,z.2)) / volume (cell q k j) ≤ positiveHorizontal f z := by
    have h : (∫⁻ x in cell q k j, f (x,z.2)) / volume (cell q k j) ≤
        positiveGridHorizontal q f z :=
      average_le_rankedMaximal volume (fun p : LineCellIndex => cell q p.1 p.2)
        (fun x => f (x,z.2)) (k,j) (hsub hz)
    have hle : positiveGridHorizontal q f z ≤ positiveHorizontal f z := by
      change positiveGridHorizontal Q.val f z ≤
        Finset.univ.sup (fun Q : GridChoice => positiveGridHorizontal Q.val f z)
      exact Finset.le_sup (f := fun Q : GridChoice => positiveGridHorizontal Q.val f z) (Finset.mem_univ Q)
    exact h.trans hle
  have hv : volume (cell q k j) ≤ 6 * ENNReal.ofReal (2*r) := by
    rw [cell_volume,show (6:ℝ≥0∞)=ENNReal.ofReal 6 by norm_num,
      ←ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [hscale]
  calc
    _ ≤ ∫⁻ x in cell q k j, f (x,z.2) := lintegral_mono_set hsub
    _ = volume (cell q k j) * ((∫⁻ x in cell q k j, f (x,z.2)) / volume (cell q k j)) := by
      rw [mul_comm,ENNReal.div_mul_cancel hv0 hvtop]
    _ ≤ _ := mul_le_mul' hv hm

variable {ι : Type*} [Fintype ι]

theorem positiveAuxiliary_line_integral (e : ι → Plane ≃ᵐ (ℝ × ℝ)) (f : Plane → ℝ≥0∞)
    (i : ι) (c r : ℝ) (hr : 0 < r) (x : Plane) (hx : (e i x).1 ∈ Icc (c-r) (c+r)) :
    (∫⁻ t in Icc (c-r) (c+r), f ((e i).symm (t,(e i x).2))) ≤
      6 * ENNReal.ofReal (2*r) * positiveAuxiliary e f x := by
  have h := positiveHorizontal_interval (f ∘ (e i).symm) c r hr (e i x) hx
  refine h.trans (mul_le_mul' le_rfl ?_)
  exact (Finset.le_sup (f := fun j => positiveChartLine (e j) f x) (Finset.mem_univ i)).trans le_sup_right

theorem positiveAuxiliary_square_integral (e : ι → Plane ≃ᵐ (ℝ × ℝ)) (f : Plane → ℝ≥0∞)
    (c : ℝ × ℝ) (r : ℝ) (hr : 0 < r) (x : Plane)
    (hx : planeCoordinates.symm x ∈ centeredSquare c r) :
    (∫⁻ z in centeredSquare c r, f (planeCoordinates z) ∂volume.prod volume) ≤
      36 * (volume.prod volume) (centeredSquare c r) * positiveAuxiliary e f x := by
  have h := square_integral_le_squareSup (f ∘ planeCoordinates) c r hr hx
  exact h.trans (mul_le_mul' le_rfl le_sup_left)

end LipschitzHilbert

end

end OAI
