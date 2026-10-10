import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import OAI.Geometry.NodalSets.Charts.QuadraticChart

namespace OAI

namespace Yau.Geometry
open scoped ContDiff

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance clmTopology {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    TopologicalSpace (E →L[ℝ] F) :=
  (ContinuousLinearMap.toNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] F)).toUniformSpace.toTopologicalSpace
local instance clmAdd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    AddCommGroup (E →L[ℝ] F) :=
  (ContinuousLinearMap.toNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] F)).toAddCommGroup
local instance clmModule {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Module ℝ (E →L[ℝ] F) :=
  (ContinuousLinearMap.toNormedSpace : NormedSpace ℝ (E →L[ℝ] F)).toModule

lemma quadraticChartMap_fderiv (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u) (x : E) :
    fderiv ℝ (quadraticChartMap y e B) x = e.toContinuousLinearMap - B x := by
  rw [(quadraticChartMap_hasFDerivAt y e B x).fderiv]
  congr 1
  ext v
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.flip_apply]
  rw [hB v x]
  module

lemma quadraticChartMap_second (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u) (x : E) :
    HasFDerivAt (fderiv ℝ (quadraticChartMap y e B)) (-B) x := by
  have heq : fderiv ℝ (quadraticChartMap y e B) = fun z ↦ e.toContinuousLinearMap - B z :=
    funext (quadraticChartMap_fderiv y e B hB)
  rw [heq]
  convert (hasFDerivAt_const e.toContinuousLinearMap x).sub B.hasFDerivAt using 1
  first | rfl | simp only [zero_sub]

def pullbackMetric (g : E → E →L[ℝ] E →L[ℝ] ℝ) (F : E → E) (x u v : E) : ℝ :=
  g (F x) (fderiv ℝ F x u) (fderiv ℝ F x v)

lemma pullbackMetric_quadratic_zero (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (u v : E) :
    pullbackMetric g (quadraticChartMap y e B) 0 u v = g y (e u) (e v) := by
  simp [pullbackMetric, quadraticChartMap_zero, (quadraticChartMap_deriv_zero y e B).fderiv]

lemma pullbackMetric_quadratic_hasFDerivAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (y : E)
    (hg : HasFDerivAt g D y) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u) (u v : E) :
    ∃ L : E →L[ℝ] ℝ,
      HasFDerivAt (fun x ↦ pullbackMetric g (quadraticChartMap y e B) x u v) L 0 ∧
      ∀ w, L w = D (e w) (e u) (e v) -
        g y (B w u) (e v) - g y (e u) (B w v) := by
  let F := quadraticChartMap y e B
  have hF : HasFDerivAt F e.toContinuousLinearMap 0 := quadraticChartMap_deriv_zero y e B
  have hd := quadraticChartMap_second y e B hB (0:E)
  have hu := (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp 0 hd
  have hv := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp 0 hd
  have hg' : HasFDerivAt g D (F 0) := by simpa [F, quadraticChartMap_zero] using hg
  have hgF := hg'.comp 0 hF
  have hp := (hgF.clm_apply hu).clm_apply hv
  refine ⟨_, hp, ?_⟩
  intro w
  simp [F, quadraticChartMap_zero, hF.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring

theorem quadratic_chart_metric_first_zero (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (y : E)
    (hg : HasFDerivAt g D y) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u)
    (hcancel : ∀ w u v, D (e w) (e u) (e v) =
      g y (B w u) (e v) + g y (e u) (B w v)) (u v : E) :
    fderiv ℝ (fun x ↦ pullbackMetric g (quadraticChartMap y e B) x u v) 0 = 0 := by
  obtain ⟨L, hL, he⟩ := pullbackMetric_quadratic_hasFDerivAt g D y hg e B hB u v
  rw [hL.fderiv]
  ext w
  rw [he, hcancel]
  simp

end
end Yau.Geometry

end OAI
