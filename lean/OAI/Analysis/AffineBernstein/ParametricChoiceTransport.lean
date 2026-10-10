import Mathlib
import OAI.Analysis.AffineBernstein.ParametricTransport
import OAI.Analysis.AffineBernstein.ParametricChoices

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma affineParametric_conormal_null {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hβ : ContDiffAt ℝ ∞ β x)
    (ha : ∀ k, ContDiffAt ℝ ∞ (a k) x) (t : ℝ)
    (hJ : (graphVariationJacobian a (t,x)).det ≠ 0)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    ((graphParamConormal u β a x t).comp L.symm.toContinuousLinearMap).comp
      (fderiv ℝ (fun y => L (graphParamVariation u β a t y)+v) x) = 0 := by
  have hX := contDiffAt_graphParamVariation hu hβ ha t
  have hd := ((L.hasFDerivAt.comp x (hX.differentiableAt (by simp)).hasFDerivAt).add_const v).fderiv
  have hd' : fderiv ℝ (fun y => L (graphParamVariation u β a t y)+v) x =
      L.toContinuousLinearMap.comp (fderiv ℝ (graphParamVariation u β a t) x) := by
    convert! hd using 1
  rw [hd']
  have hh := graphParamConormal_null (hu.differentiableAt (by simp))
    (hβ.differentiableAt (by simp)) (fun k => (ha k).differentiableAt (by simp)) t hJ
  ext w
  simpa using congrArg (fun f : Space n →L[ℝ] ℝ => f w) hh

/- The ambient conormal/transverse choices in the local chart stationarity
functional may be replaced by any other inward normalized choices. -/
theorem coordinateAffineVariationArea_choices {n : ℕ}
    {Ω U : Set (Space n)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiff ℝ ∞ β)
    (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {φ : Space n → Space n} (hφ : ContDiffOn ℝ ∞ φ U) (hφΩ : φ '' U ⊆ Ω)
    {x : Space n} (hx : x ∈ U) (hφJ : (parametricJacobian φ x).det ≠ 0) (t : ℝ)
    (hJ : (graphVariationJacobian a (t,φ x)).det ≠ 0)
    (hH : 0 ≤ (graphVariationSecond u β a (t,φ x)).det)
    (ν : (Space n × ℝ) →L[ℝ] ℝ) (ξ : Space n × ℝ)
    (hν : ν.comp (fderiv ℝ ((fun y => L (graphParamVariation u β a t y)+v) ∘ φ) x) = 0)
    (hξ : ν ξ = 1) (hc : 0 < ν (L ((0 : Space n),1))) :
    parametricAreaDensity (graphAmbientBasis n)
      ((fun y => L (graphParamVariation u β a t y)+v) ∘ φ) ν ξ x =
      coordinateAffineVariationArea L v φ u β a x t := by
  let X := fun y => L (graphParamVariation u β a t y)+v
  let μ := (graphParamConormal u β a (φ x) t).comp L.symm.toContinuousLinearMap
  have hxΩ := hφΩ (mem_image_of_mem φ hx)
  have huc := hu.contDiffAt (hΩ.mem_nhds hxΩ)
  have hφc := hφ.contDiffAt (hU.mem_nhds hx)
  have hW := contDiffAt_graphParamVariation huc hβ.contDiffAt (fun k => (ha k).contDiffAt) t
  have hX : ContDiffAt ℝ ∞ X (φ x) := (L.contDiff.contDiffAt.comp (φ x) hW).add contDiffAt_const
  have hμ : μ.comp (fderiv ℝ X (φ x)) = 0 := affineParametric_conormal_null huc
    hβ.contDiffAt (fun k => (ha k).contDiffAt) t hJ L v
  have hμc : μ.comp (fderiv ℝ (X ∘ φ) x) = 0 := by
    rw [fderiv_comp x (hX.differentiableAt (by simp)) (hφc.differentiableAt (by simp))]
    rw [← ContinuousLinearMap.comp_assoc,hμ,ContinuousLinearMap.zero_comp]
  have hfull : ContDiffOn ℝ ∞ (X ∘ φ) U := by
    intro z hz
    have huz := hu.contDiffAt (hΩ.mem_nhds (hφΩ (mem_image_of_mem φ hz)))
    have hWz := contDiffAt_graphParamVariation huz hβ.contDiffAt (fun k => (ha k).contDiffAt) t
    exact (((L.contDiff.contDiffAt.comp (φ z) hWz).add contDiffAt_const).comp z
      (hφ.contDiffAt (hU.mem_nhds hz))).contDiffWithinAt
  have hdet : (graphAmbientBasis n).det (parametricFrame (X ∘ φ) (L ((0 : Space n),1)) x) ≠ 0 := by
    rw [parametricFrame_comp_det _ (hX.differentiableAt (by simp)) (hφc.differentiableAt (by simp))]
    apply mul_ne_zero _ hφJ
    change (graphAmbientBasis n).det (parametricFrame (fun y => L (graphParamVariation u β a t y)+v)
      (L ((0 : Space n),1)) (φ x)) ≠ 0
    rw [parametricFrame_affine (hW.differentiableAt (by simp)),Module.Basis.det_comp]
    apply mul_ne_zero
    · rw [← LinearMap.det_toMatrix (graphAmbientBasis n)]
      exact (L.toLinearEquiv.isUnit_det _ _).ne_zero
    · rw [graphParam_frame_determinant (huc.differentiableAt (by simp))
        (hβ.contDiffAt.differentiableAt (by simp))
        (fun k => (ha k).contDiffAt.differentiableAt (by simp)) t]
      exact hJ
  have hsecond : 0 ≤ (parametricSecondForm (X ∘ φ) μ x).det := by
    rw [parametricSecondForm_comp hX hφc μ hμ]
    change 0 ≤ ((parametricJacobian φ x).transpose *
      parametricSecondForm (fun y => L (graphParamVariation u β a t y)+v)
        ((graphParamConormal u β a (φ x) t).comp L.symm.toContinuousLinearMap) (φ x) * _).det
    rw [parametricSecondForm_affine,graphParam_secondForm hΩ hu hβ.contDiffOn (fun k => (ha k).contDiffOn) hxΩ,
      Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
    change 0 ≤ (parametricJacobian φ x).det * (graphVariationSecond u β a (t,φ x)).det * (parametricJacobian φ x).det
    nlinarith [sq_nonneg (parametricJacobian φ x).det]
  exact parametricAreaDensity_choices (graphAmbientBasis n) hU hfull hx μ ν
    (L ((0 : Space n),1)) ξ hdet hμc hν (by simp [μ]) hξ hc hsecond

end AffineBernstein
end

end OAI
