import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def quadraticChartMap (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (x : E) : E :=
  y + e x - (1/2:ℝ) • B x x

lemma quadraticChartMap_smooth (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    ContDiff ℝ ∞ (quadraticChartMap y e B) := by
  exact (contDiff_const.add e.contDiff).sub
    (B.contDiff.clm_apply contDiff_id |>.const_smul (1/2:ℝ))

lemma quadraticChartMap_zero (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    quadraticChartMap y e B 0 = y := by simp [quadraticChartMap]

lemma quadraticChartMap_hasFDerivAt (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (x : E) :
    HasFDerivAt (quadraticChartMap y e B)
      (e.toContinuousLinearMap - (1/2:ℝ) • (B.flip x + B x)) x := by
  have h := (B.hasFDerivAt.clm_apply (hasFDerivAt_id x))
  convert ((hasFDerivAt_const y x).add e.hasFDerivAt).sub (h.const_smul (1/2:ℝ)) using 1 <;>
    simp [add_comm]
  funext z
  simp [quadraticChartMap, add_comm]

lemma quadraticChartMap_deriv_zero (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) :
    HasFDerivAt (quadraticChartMap y e B) e.toContinuousLinearMap 0 := by
  simpa using quadraticChartMap_hasFDerivAt y e B 0

variable [CompleteSpace E]

def quadraticChart (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    OpenPartialHomeomorph E E :=
  (quadraticChartMap_smooth y e B).contDiffAt.toOpenPartialHomeomorph
    (quadraticChartMap y e B) (quadraticChartMap_deriv_zero y e B) (by simp)

lemma quadraticChart_coe (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    (quadraticChart y e B : E → E) = quadraticChartMap y e B := rfl

lemma quadraticChart_source (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    0 ∈ (quadraticChart y e B).source :=
  ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _

lemma quadraticChart_target (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    y ∈ (quadraticChart y e B).target := by
  simpa [quadraticChart_coe, quadraticChartMap_zero] using
    (quadraticChart y e B).map_source (quadraticChart_source y e B)

lemma quadraticChart_inverse_smooth (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) :
    ContDiffAt ℝ ∞ (quadraticChart y e B).symm y := by
  have h := (quadraticChartMap_smooth y e B).contDiffAt.to_localInverse
    (quadraticChartMap_deriv_zero y e B) (by simp)
  simpa [ContDiffAt.localInverse, quadraticChart, ContDiffAt.toOpenPartialHomeomorph, HasStrictFDerivAt.localInverse, quadraticChartMap_zero] using h

end
end Yau.Geometry

end OAI
