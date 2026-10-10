import OAI.MeasureTheory.Falconer.Measures.FourSpatialPairMeasure

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

noncomputable def fourCells (d e : PositiveDistanceData) : Fin 4 → Measure Plane :=
  ![d.ρ.restrict (d.Q.descendant d.X).carrier,d.ρ.restrict (d.Q.descendant d.Y).carrier,
    e.ρ.restrict (e.Q.descendant e.X).carrier,e.ρ.restrict (e.Q.descendant e.Y).carrier]

instance fourCells_finite (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (i : Fin 4) :
    IsFiniteMeasure (fourCells d e i) := by
  fin_cases i <;> dsimp [fourCells] <;> infer_instance

theorem fourCells_preserving (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] :
    MeasurePreserving fourSpatialPairEquiv (Measure.pi (fourCells d e))
      (d.cellPair.prod e.cellPair) := measurePreserving_fourSpatialPair (fourCells d e)

theorem coincidence_original_four (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.coincidence = d.normalization * (Measure.pi (fourCells d d))
      {x | |dist (x 0) (x 1)-dist (x 2) (x 3)| ≤ 100*d.width ∧
        (x 0,x 1) ∈ d.good ∧ (x 2,x 3) ∈ d.good} := by
  rw [d.coincidence_four_point]
  congr 1
  let C : Set ((Plane × Plane) × (Plane × Plane)) :=
    {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width ∧
      z.1 ∈ d.good ∧ z.2 ∈ d.good}
  have hC : MeasurableSet C := by
    change MeasurableSet ({z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width} ∩
      (d.good ×ˢ d.good))
    apply MeasurableSet.inter
    · exact measurableSet_le (by fun_prop) measurable_const
    · exact d.measurable_good.prod d.measurable_good
  exact ((fourCells_preserving d d).measure_preimage hC.nullMeasurableSet).symm

theorem original_spatial_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (S : Set ((Plane × Plane) × (Plane × Plane))) (hS : MeasurableSet S) :
    ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a))) *
      (∫⁻ x in fourSpatialPairEquiv ⁻¹' (S ∩ (d.good ×ˢ e.good)), ENNReal.ofReal
        (1/(1+(2:ℝ)^d.t*|dist (x 0) (x 1)-dist (x 2) (x 3)|)^2)
        ∂Measure.pi (fourCells d e)) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a))) * max d.coincidence e.coincidence := by
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ≥0∞ := fun z => ENNReal.ofReal
    (1/(1+(2:ℝ)^d.t*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
  have hF : Measurable F := by unfold F; fun_prop
  have he := (fourCells_preserving d e).setLIntegral_comp_preimage
    (hS.inter (d.measurable_good.prod e.measurable_good)) hF
  change (∫⁻ x in fourSpatialPairEquiv ⁻¹' (S ∩ (d.good ×ˢ e.good)),
    ENNReal.ofReal (1/(1+(2:ℝ)^d.t*|dist (x 0) (x 1)-dist (x 2) (x 3)|)^2)
    ∂Measure.pi (fourCells d e)) = _ at he
  rw [he]
  have hr : (d.cellPair.prod e.cellPair).restrict (S ∩ (d.good ×ˢ e.good)) =
      (d.pair.prod e.pair).restrict S := by
    rw [pair,pair,Measure.prod_restrict,Measure.restrict_restrict hS]
  rw [hr]
  exact spatial_stationary_kernel_max d e ht hn S

end PositiveDistanceData

end PlanarFalconer

end OAI
