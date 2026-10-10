import OAI.Analysis.LipschitzHilbert.Geometry.DirectionChartSampling
import OAI.Analysis.LipschitzHilbert.Estimates.PlaneSlopeLipschitz
import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram

namespace OAI

/-! The orthogonal chart and product coordinates preserve the input L2
norm. The slope and endpoint factors satisfy global quantitative bounds. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace LipschitzHilbert

def chartCoordinateMap (d : Plane) : (ℝ×ℝ) ≃L[ℝ] Plane :=
  planeCoordinatesContinuous.trans (directionChart d).symm.toContinuousLinearEquiv

def chartSchwartz (d : Plane) (f : SchwartzMap Plane ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (chartCoordinateMap d) f

@[simp] theorem chartSchwartz_apply (d : Plane) (f : SchwartzMap Plane ℂ) (z : ℝ×ℝ) :
    chartSchwartz d f z=f ((directionChart d).symm (planeCoordinates z)) := rfl

theorem chartCoordinateMap_measurePreserving (d : Plane) :
    MeasurePreserving (chartCoordinateMap d) (volume.prod volume) volume :=
  (directionChart d).symm.measurePreserving.comp planeCoordinates_measurePreserving

theorem chartSchwartz_norm (d : Plane) (f : SchwartzMap Plane ℂ) :
    ‖(chartSchwartz d f).toLp 2 (volume.prod volume)‖=‖f.toLp 2 volume‖ := by
  simp only [SchwartzMap.toLp, Lp.norm_toLp]
  congr 1
  exact eLpNorm_comp_measurePreserving (f.memLp 2 volume).aestronglyMeasurable
    (chartCoordinateMap_measurePreserving d)

theorem chartInverse_measurePreserving (d : Plane) :
    MeasurePreserving (fun x => planeCoordinates.symm (directionChart d x))
      volume (volume.prod volume) :=
  planeCoordinates_measurePreserving.symm.comp (directionChart d).measurePreserving

theorem chartDenominator_bounds (v : Plane → Plane) (hv : ∀ x, ‖v x‖=1) (x : Plane) :
    1/2≤chartDenominator v x ∧ chartDenominator v x≤1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  have hc : |v x 0|≤1 := by
    simpa only [Real.norm_eq_abs,hv x] using PiLp.norm_apply_le (v x) (0 : Fin 2)
  exact (le_abs_self _).trans hc

theorem clippedChartSlope_small_lipschitz (v : Plane → Plane)
    (hv : LipschitzWith (1/100) v) (hunit : ∀ x, ‖v x‖=1) :
    LipschitzWith 1 (clippedChartSlope v) :=
  (clippedChartSlope_lipschitz hv hunit).weaken (by
    exact_mod_cast (show (6:ℝ)*(1/100)≤1 by norm_num))

theorem chartDenominator_measurable (v : Plane → Plane) {K : ℝ≥0}
    (hv : LipschitzWith K v) : Measurable (chartDenominator v) :=
  ((coordinate_lipschitz hv 0).const_max (1/2)).continuous.measurable

theorem shortTransform_clippedChart (v : Plane → Plane) (x : Plane)
    (epsilon R : ℝ) (f : Plane → ℂ) (h0 : 9/10<v x 0) (h1 : |v x 1|<1/10) :
    shortTransform v epsilon R f x=
      PacketRepresentation.productSymmetricTruncation
        (fun z => clippedChartSlope v (planeCoordinates z))
        (epsilon*chartDenominator v x) (R*chartDenominator v x)
        (f ∘ planeCoordinates) (planeCoordinates.symm x) := by
  have hs := clippedChartSlope_eq_ratio h0 h1
  have hd : chartDenominator v x=v x 0 := max_eq_right (by linarith)
  rw [shortTransform_as_slope v x epsilon R f (by linarith),hd]
  simp only [PacketRepresentation.productSymmetricTruncation,
    PacketRepresentation.productSlopeSample,MeasurableEquiv.apply_symm_apply,hs]

end LipschitzHilbert

end

end OAI
