import OAI.Analysis.LipschitzHilbert.Geometry.RectangleLineCoordinates
import OAI.Analysis.LipschitzHilbert.Geometry.LaceyLiSelectionCover

namespace OAI

/-! The near-angle intersection sum is controlled by the actual
auxiliary maximal function, pointwise on the target rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
variable {ι κ : Type*} [Fintype κ]

theorem near_intersection_sum_le_auxiliary (D : κ → Rectangle) (R : ι → Rectangle)
    (s : Finset ι) (T : Rectangle) (i : κ) (A : ℝ) (hA : 0 ≤ A)
    (hL : ∀ j ∈ s, T.long ≤ (R j).long)
    (hangle : ∀ j ∈ s, T.long * dist ((R j).axes 0) (T.axes 0) ≤ A*T.short)
    (htrans : ∀ j ∈ s, 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1|)
    (x : Plane) (hx : x ∈ T.carrier) :
    (∑ j ∈ s, volume (T.carrier ∩ (R j).carrier)) ≤
      ENNReal.ofReal (96*(A+1)) * volume T.carrier *
        positiveAuxiliary (fun i => (D i).orthogonalCoordinates)
          (rectangleCount (fun j => (R j).dilate (4*(A+1)+5) (by linarith)) s) x := by
  let a := 4*(A+1)+5
  have ha : 0 < a := by dsimp [a]; linarith
  let g := rectangleCount (fun j => (R j).dilate a ha) s
  let e := (D i).orthogonalCoordinates
  let c := (e x).1
  let b := (e x).2
  let r := 2*(A+1)*T.short
  have hr : 0 < r := mul_pos (by linarith) T.short_pos
  let I := Icc (c-r) (c+r)
  let P := fun u : ℝ => e.symm (u,b)
  have hP : Measurable P := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hint (j : ι) : Measurable (fun u => ((R j).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u)) :=
    (measurable_const.indicator ((R j).dilate a ha).measurableSet_carrier).comp hP
  have hsum : (∫⁻ u in I, g (P u)) = ∑ j ∈ s,
      ∫⁻ u in I, ((R j).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    exact lintegral_finsetSum s (fun j _ => hint j)
  have hterm (j : ι) (hj : j ∈ s) : volume (T.carrier ∩ (R j).carrier) ≤
      ENNReal.ofReal (4*T.long) * ∫⁻ u in I,
        ((R j).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    by_cases hn : (T.carrier ∩ (R j).carrier).Nonempty
    · exact Rectangle.near_intersection_line_integral T (R j) (D i) x hx hn (hL j hj)
        A hA (hangle j hj) (htrans j hj)
    · rw [Set.not_nonempty_iff_eq_empty.mp hn,measure_empty]
      exact zero_le
  have haux := positiveAuxiliary_line_integral (fun j => (D j).orthogonalCoordinates)
    g i c r hr x (show (e x).1 ∈ Icc (c-r) (c+r) by constructor <;> dsimp [c] <;> linarith)
  have hc : ENNReal.ofReal (4*T.long)*6*ENNReal.ofReal (2*r) =
      ENNReal.ofReal (96*(A+1))*volume T.carrier := by
    have hp4 : 0 ≤ 4*T.long := mul_nonneg (by norm_num) T.long_pos.le
    have hp96 : 0 ≤ 96*(A+1) := mul_nonneg (by norm_num) (by linarith)
    calc
      _ = ENNReal.ofReal ((4*T.long)*6*(2*r)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hp4 (by norm_num)),ENNReal.ofReal_mul hp4]
        norm_num
      _ = ENNReal.ofReal ((96*(A+1))*T.long*T.short) := by congr 1; dsimp [r]; ring
      _ = _ := by
        rw [Rectangle.volume_carrier,ENNReal.ofReal_mul (mul_nonneg hp96 T.long_pos.le),ENNReal.ofReal_mul hp96]
        ring
  calc
    _ ≤ ∑ j ∈ s, ENNReal.ofReal (4*T.long) * ∫⁻ u in I,
        ((R j).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (4*T.long) * ∫⁻ u in I, g (P u) := by rw [hsum,Finset.mul_sum]
    _ ≤ ENNReal.ofReal (4*T.long) * (6*ENNReal.ofReal (2*r)*
        positiveAuxiliary (fun j => (D j).orthogonalCoordinates) g x) := mul_le_mul' le_rfl haux
    _ = _ := by rw [←mul_assoc,←mul_assoc,hc]

end LipschitzHilbert

end

end OAI
