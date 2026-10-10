import OAI.MeasureTheory.Falconer.Angular.GnomonicLaw
import OAI.MeasureTheory.Falconer.Slicing.GaussianCloseMass

namespace OAI

/-! # Gaussian direction slices retain the original affine chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

noncomputable def gaussianChartSliceMeasure (μ : Measure (Space n))
    (A : Fin h → Space (n+1)) (r : ℝ) : Measure (Space n) :=
  ENNReal.ofReal (r^(-(h:ℝ))) •
    μ.restrict (gnomonicChart ⁻¹' gaussianDirectionBand A r)

theorem gnomonic_chart_law_recover (μ : Measure (Space n)) :
    Measure.map gnomonicCoordinates (Measure.map gnomonicChart μ) = μ := by
  rw [Measure.map_map gnomonicCoordinates_measurable (gnomonicChart_continuous n).measurable]
  have he : gnomonicCoordinates ∘ gnomonicChart = (id : Space n → Space n) := by
    funext p
    exact gnomonicCoordinates_gnomonicChart p
  rw [he,Measure.map_id]

theorem gaussianChartSlice_map (μ : Measure (Space n))
    (A : Fin h → Space (n+1)) (r : ℝ) :
    Measure.map gnomonicChart (gaussianChartSliceMeasure μ A r) =
      gaussianDirectionSliceMeasure (Measure.map gnomonicChart μ) A r := by
  unfold gaussianChartSliceMeasure gaussianDirectionSliceMeasure
  rw [Measure.map_smul _ (gnomonicChart_continuous n).measurable.aemeasurable,
    Measure.restrict_map (gnomonicChart_continuous n).measurable (gaussianDirectionBand_measurable A r)]

theorem gaussianChartSlice_recover (μ : Measure (Space n))
    (A : Fin h → Space (n+1)) (r : ℝ) :
    Measure.map gnomonicCoordinates
      (gaussianDirectionSliceMeasure (Measure.map gnomonicChart μ) A r) =
        gaussianChartSliceMeasure μ A r := by
  rw [← gaussianChartSlice_map,gnomonic_chart_law_recover]

end Falconer

end OAI
