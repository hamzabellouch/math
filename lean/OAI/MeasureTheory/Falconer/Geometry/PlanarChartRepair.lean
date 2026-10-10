import OAI.MeasureTheory.Falconer.Slicing.PlanarSliceGeometry

namespace OAI

/-! # Choosing bounded representatives of almost-everywhere planar chart maps -/

namespace Falconer
open Set MeasureTheory

noncomputable def boundedPlanarPoint (x : Space 2) : Space 2 :=
  if ‖x‖ ≤ 1/4 then x else 0

noncomputable def chartedPlanarDirection (w : Space 2) : Space 2 :=
  if ‖w‖ = 1 ∧ dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 then w
  else EuclideanSpace.basisFun (Fin 2) ℝ 0

theorem boundedPlanarPoint_measurable : Measurable boundedPlanarPoint := by
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_id measurable_const

theorem chartedPlanarDirection_measurable : Measurable chartedPlanarDirection := by
  have hn : Measurable (fun w : Space 2 => ‖w‖) := continuous_norm.measurable
  have hd : Measurable (fun w : Space 2 => dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0)) :=
    (continuous_id.dist continuous_const).measurable
  have hQ : MeasurableSet {w : Space 2 | ‖w‖ = 1 ∧
      dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4} :=
    (measurableSet_eq_fun hn measurable_const).inter
      (measurableSet_le hd measurable_const)
  exact Measurable.ite hQ measurable_id measurable_const

theorem boundedPlanarPoint_norm (x : Space 2) : ‖boundedPlanarPoint x‖ ≤ 1/4 := by
  unfold boundedPlanarPoint
  split_ifs with hx
  · exact hx
  · simp

theorem chartedPlanarDirection_unit (w : Space 2) : ‖chartedPlanarDirection w‖ = 1 := by
  unfold chartedPlanarDirection
  split_ifs with hw
  · exact hw.1
  · exact (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one 0

theorem chartedPlanarDirection_chart (w : Space 2) :
    dist (chartedPlanarDirection w) (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
  unfold chartedPlanarDirection
  split_ifs with hw
  · exact hw.2
  · simp

theorem boundedPlanarPoint_eq {x : Space 2} (hx : ‖x‖ ≤ 1/4) : boundedPlanarPoint x = x :=
  ite_eq_left hx

theorem chartedPlanarDirection_eq {w : Space 2}
    (hw : ‖w‖ = 1 ∧ dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) :
    chartedPlanarDirection w = w := ite_eq_left hw

end Falconer

end OAI
