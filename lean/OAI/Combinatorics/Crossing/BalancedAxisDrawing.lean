import OAI.Combinatorics.Crossing.AxisAdmissibility
import OAI.Combinatorics.Crossing.BalancedAxisIntervals

namespace OAI

noncomputable section
namespace Zarankiewicz

structure BalancedAxisRealization (m n : ℕ) where
  vertical : Fin m → ℝ
  horizontal : Fin n → ℝ
  vertical_interval : ∀ i, vertical i ∈ Set.Ioo (axisIntervalLo m i) (axisIntervalHi m i)
  horizontal_interval : ∀ p, horizontal p ∈ Set.Ioo (axisIntervalLo n p) (axisIntervalHi n p)
  generic : ∀ e f g : BipartiteEdge m n, AxisIndependentTriple e f g →
    axisConcurrency (vertical e.1) (horizontal e.2) (vertical f.1) (horizontal f.2)
      (vertical g.1) (horizontal g.2) ≠ 0

theorem nonempty_balancedAxisRealization (m n : ℕ) : Nonempty (BalancedAxisRealization m n) := by
  let lo : BipartiteVertex m n → ℝ
    | .inl i => axisIntervalLo m i
    | .inr p => axisIntervalLo n p
  let hi : BipartiteVertex m n → ℝ
    | .inl i => axisIntervalHi m i
    | .inr p => axisIntervalHi n p
  have hinterval : ∀ j, lo j < hi j := by
    rintro (i|p)
    · exact axisInterval_nonempty m i
    · exact axisInterval_nonempty n p
  obtain ⟨x,hx,hgeneric⟩ := exists_axis_generic_positions lo hi hinterval
  exact ⟨⟨fun i => x (Sum.inl i),fun p => x (Sum.inr p),fun i => hx (Sum.inl i),
    fun p => hx (Sum.inr p),hgeneric⟩⟩

namespace BalancedAxisRealization
variable {m n : ℕ} (R : BalancedAxisRealization m n)

theorem vertical_injective : Function.Injective R.vertical := axisInterval_injective m _ R.vertical_interval
theorem horizontal_injective : Function.Injective R.horizontal := axisInterval_injective n _ R.horizontal_interval
theorem vertical_ne_zero (i : Fin m) : R.vertical i ≠ 0 := axisInterval_ne_zero m i _ (R.vertical_interval i)
theorem horizontal_ne_zero (p : Fin n) : R.horizontal p ≠ 0 := axisInterval_ne_zero n p _ (R.horizontal_interval p)
theorem vertical_abs_strictMono : StrictMono (fun i => |R.vertical i|) := axisInterval_abs_strictMono m _ R.vertical_interval
theorem horizontal_abs_strictMono : StrictMono (fun p => |R.horizontal p|) := axisInterval_abs_strictMono n _ R.horizontal_interval

def drawing : AdmissibleDrawing m n :=
  axisAdmissibleDrawing R.vertical R.horizontal R.vertical_injective R.horizontal_injective
    R.vertical_ne_zero R.horizontal_ne_zero R.generic

theorem drawing_noAdjacent : NoAdjacentCrossings R.drawing :=
  axisAdmissibleDrawing_noAdjacent _ _ _ _ _ _ _

theorem drawing_vertex_left (i : Fin m) : R.drawing.vertex (Sum.inl i)=(0,R.vertical i) := rfl
theorem drawing_vertex_right (p : Fin n) : R.drawing.vertex (Sum.inr p)=(R.horizontal p,0) := rfl
theorem drawing_edge (e : BipartiteEdge m n) :
    R.drawing.edge e=Path.segment (0,R.vertical e.1) (R.horizontal e.2,0) := rfl

theorem drawing_edgeInterior (e : BipartiteEdge m n) :
    edgeInterior R.drawing.toContinuousDrawing e=openSegmentTrace (0,R.vertical e.1) (R.horizontal e.2,0) :=
  axisContinuousDrawing_interior R.vertical R.horizontal R.vertical_injective R.horizontal_injective
    R.vertical_ne_zero R.horizontal_ne_zero e

end BalancedAxisRealization

theorem exists_axis_admissible (m n : ℕ) : Nonempty (AdmissibleDrawing m n) := by
  obtain ⟨R⟩ := nonempty_balancedAxisRealization m n
  exact ⟨R.drawing⟩

end Zarankiewicz

end

end OAI
