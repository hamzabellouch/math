import OAI.MeasureTheory.Falconer.Slicing.GaussianBand
import OAI.MeasureTheory.Falconer.Slicing.SliceGeometry

namespace OAI

/-! # The exact Gaussian law of an orthogonal projection -/

namespace Falconer
open MeasureTheory ProbabilityTheory
variable {d : ℕ}

theorem gaussian_orthogonal_projection (V : Submodule ℝ (Space d)) :
    (stdGaussian (Space d)).map V.orthogonalProjectionOnto = stdGaussian V := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply,integral_map V.orthogonalProjectionOnto.continuous.measurable.aemeasurable
    (by fun_prop)]
  simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← charFun_apply,charFun_stdGaussian,charFun_stdGaussian]
  rfl

end Falconer

end OAI
