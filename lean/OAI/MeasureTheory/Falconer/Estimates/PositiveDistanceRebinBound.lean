import OAI.MeasureTheory.Falconer.Estimates.ComparablePositiveRebin
import OAI.MeasureTheory.Falconer.Fourier.GoodSupportedKernelMajorant

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace PositiveDistanceData

abbrev atCells (d : PositiveDistanceData) (X Y : CellPath) : PositiveDistanceData :=
  {d with X := X, Y := Y}

theorem angularFourCellMeasure_eq (d e : PositiveDistanceData) (row col : CellPath × CellPath) :
    angularFourCellMeasure d.Q e.Q d.ρ e.ρ row col =
      Measure.pi (fourCells (d.atCells row.1 col.1) (e.atCells row.2 col.2)) := by
  unfold angularFourCellMeasure
  congr 1
  funext j
  fin_cases j <;> rfl

theorem cell_shell_positive_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (row col : CellPath × CellPath) (b : ℕ) :
    ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a))) *
      (∫⁻ x in angularLengthShell b,
        (fourPairGood d.good e.good).indicator (distanceDifferenceKernel d.t) x
          ∂angularFourCellMeasure d.Q e.Q d.ρ e.ρ row col) ≤
      binKernelConstant * ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a))) *
        max (d.atCells row.1 col.1).coincidence (e.atCells row.2 col.2).coincidence := by
  let D := d.atCells row.1 col.1
  let E := e.atCells row.2 col.2
  let T := fourSpatialPairEquiv.symm ⁻¹' angularLengthShell b
  have hT : MeasurableSet T := (measurable_angularLengthShell b).preimage fourSpatialPairEquiv.symm.measurable
  have he : fourPairGood d.good e.good ∩ angularLengthShell b =
      fourSpatialPairEquiv ⁻¹' (T ∩ (D.good ×ˢ E.good)) := by
    ext x
    simp only [T,D,E,good,fourPairGood,mem_inter_iff,mem_preimage,
      MeasurableEquiv.symm_apply_apply]
    exact and_comm
  rw [lintegral_indicator (measurable_fourPairGood d.measurable_good e.measurable_good),
    Measure.restrict_restrict (measurable_fourPairGood d.measurable_good e.measurable_good),
    he,angularFourCellMeasure_eq]
  simpa only [D,E,atCells,levelMass,distanceDifferenceKernel,Real.rpow_natCast] using
    original_spatial_kernel_max D E ht hn T hT

theorem rebinned_positive_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (A B : CellPath) (n b : ℕ) :
    ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a))) *
      (∑ row ∈ sourceProductVertices d.Q e.Q d.ρ e.ρ A B n,
        ∑ col ∈ sourceProductVertices d.Q e.Q d.ρ e.ρ A B n,
          if angularSeparated d.Q e.Q b row col then
            ∫⁻ x in angularLengthShell b,
              (fourPairGood d.good e.good).indicator (distanceDifferenceKernel d.t) x
                ∂angularFourCellMeasure d.Q e.Q d.ρ e.ρ row col
          else 0) ≤
    (binKernelConstant * ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a)))) *
      ∑ row ∈ sourceProductVertices d.Q e.Q d.ρ e.ρ A B n,
        ∑ col ∈ sourceProductVertices d.Q e.Q d.ρ e.ρ A B n,
          if angularSeparated d.Q e.Q b row col then
            max (d.atCells row.1 col.1).coincidence (e.atCells row.2 col.2).coincidence
          else 0 := by
  simp only [Finset.mul_sum,mul_ite,mul_zero]
  apply Finset.sum_le_sum
  intro row hr
  apply Finset.sum_le_sum
  intro col hc
  by_cases hs : angularSeparated d.Q e.Q b row col
  · simpa only [hs,↓reduceIte] using cell_shell_positive_kernel_max d e ht hn row col b
  · simp [hs]

end PositiveDistanceData

end PlanarFalconer

end OAI
