import OAI.Geometry.SurfaceImmersion.Geometry.FlatFirstHolder
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace OAI

/-! The rank-zero stratum is null when half the domain dimension is
strictly below the target dimension. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology ENNReal NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

local instance flatNullFirstNormed : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance flatNullFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

theorem flat_first_image_null (μ : Measure F) [Measure.IsAddHaarMeasure μ]
    {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hdim : (Module.finrank ℝ E : ℝ≥0∞)/2 < Module.finrank ℝ F) :
    μ (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  let : SecondCountableTopology F := inferInstance
  let : LocallyCompactSpace F := inferInstance
  let : SigmaFinite μ := inferInstance
  have hd : dimH (f '' {x | fderiv ℝ f x = 0}) < Module.finrank ℝ F :=
    (flat_first_image_dimH hf).trans_lt hdim
  have hd' : dimH (f '' {x | fderiv ℝ f x = 0}) <
      ((Module.finrank ℝ F : ℝ≥0) : ℝ≥0∞) := by
    simpa only [ENNReal.coe_natCast] using hd
  have hh' := hausdorffMeasure_of_dimH_lt (d := (Module.finrank ℝ F : ℝ≥0)) hd'
  have hh : μH[(Module.finrank ℝ F : ℝ)] (f '' {x | fderiv ℝ f x = 0}) = 0 := by
    simpa only [NNReal.coe_natCast] using hh'
  have hμ : μ ≪ (μH[(Module.finrank ℝ F : ℝ)] : Measure F) :=
    Measure.absolutelyContinuous_isAddHaarMeasure μ (μH[(Module.finrank ℝ F : ℝ)] : Measure F)
  exact hμ hh

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
