import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ThreeRadiusNormedSpace

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
local instance threeLogNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeLogContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeLog_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma threeSphereDirection_inner (p : ThreeManifold) (i j : Fin 3) :
    inner ℝ (threeSphereDirection p i) (threeSphereDirection p j) =
      (if i=j then 1 else 0)-(p.1:Euclidean 3) i*(p.1:Euclidean 3) j := by
  simp only [threeSphereDirection,WithLp.prod_inner_apply,
    inner_zero_left,add_zero,unitSphereCoordinates_inner]
  have hi : inner ℝ (p.1:Euclidean 3) (productAxis i) = (p.1:Euclidean 3) i := by rw [real_inner_comm,productAxis_coord]
  have hj : inner ℝ (p.1:Euclidean 3) (productAxis j) = (p.1:Euclidean 3) j := by rw [real_inner_comm,productAxis_coord]
  rw [hi,hj,productAxis_coord]
  simp [productAxis,PiLp.single_apply]
lemma threeSphereDirection_fst_inner (p : ThreeManifold) (i j : Fin 3) :
    inner ℝ (threeSphereDirection p i).fst (threeSphereDirection p j).fst =
      (if i=j then 1 else 0)-(p.1:Euclidean 3) i*(p.1:Euclidean 3) j := by
  have h:=threeSphereDirection_inner p i j
  simpa [threeSphereDirection,WithLp.prod_inner_apply] using h

def threeLogEnvelope (p : ThreeManifold) (c : ℝ) (y : ThreeModel) : ℝ :=
  c/2*Real.log (threeRadiusSq p y)
lemma threeLogEnvelope_first (p : ThreeManifold) (c : ℝ) (hq : threeRadiusSq p 0 ≠ 0) (v : ThreeModel) :
    fderiv ℝ (threeLogEnvelope p c) 0 v =
      (c/2)*(threeRadiusSq p 0)⁻¹*fderiv ℝ (threeRadiusSq p) 0 v := by
  change fderiv ℝ ((c/2) • (fun y => Real.log (threeRadiusSq p y))) 0 v = _
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply,smul_apply,smul_eq_mul]
  rw [scalarLog_first ((threeRadiusSq_smooth p).differentiable (by simp) 0) hq]
  ring
lemma threeLogEnvelope_second (p : ThreeManifold) (c : ℝ) (hq : threeRadiusSq p 0 ≠ 0) (v w : ThreeModel) :
    fderiv ℝ (fderiv ℝ (threeLogEnvelope p c)) 0 v w =
      (c/2)*((threeRadiusSq p 0)⁻¹*fderiv ℝ (fderiv ℝ (threeRadiusSq p)) 0 v w-
        (threeRadiusSq p 0)⁻¹^2*fderiv ℝ (threeRadiusSq p) 0 v*fderiv ℝ (threeRadiusSq p) 0 w) := by
  change fderiv ℝ (fderiv ℝ ((c/2) • (fun y => Real.log (threeRadiusSq p y)))) 0 v w = _
  rw [fderiv_const_smul_field]
  rw [fderiv_const_smul_field (𝕜:=ℝ) (f:=fderiv ℝ (fun y => Real.log (threeRadiusSq p y))) (c/2)]
  simp only [Pi.smul_apply,smul_apply,smul_eq_mul]
  rw [scalarLog_second (threeRadiusSq_smooth p) hq]

lemma threeLogEnvelope_first_axis (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    fderiv ℝ (threeLogEnvelope p c) 0 = innerSL ℝ ((c/(p.1:Euclidean 3) 0) • threeSphereDirection p 0) := by
  have hq : threeRadiusSq p 0 ≠ 0 := by simp [threeRadiusSq_zero,hy,pow_ne_zero 2 hx]
  ext v
  rw [threeLogEnvelope_first p c hq,threeRadiusSq_first]
  simp only [threeRadiusSq_zero,hy,add_zero,mul_zero,zero_mul,innerSL_apply_apply,real_inner_smul_left]
  field_simp [hx]
  ring

lemma threeLogEnvelope_hessian_axis (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) (v w : ThreeModel) :
    actualCoordinateHessian (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0 v w =
      c/((p.1:Euclidean 3) 0)^2 *
        (inner ℝ (threeSphereDirection p 1) v*inner ℝ (threeSphereDirection p 1) w-
        inner ℝ (threeSphereDirection p 0) v*inner ℝ (threeSphereDirection p 0) w)-
      c*inner ℝ v.fst w.fst := by
  have hq : threeRadiusSq p 0 ≠ 0 := by simp [threeRadiusSq_zero,hy,pow_ne_zero 2 hx]
  rw [threeChartMetric_background_hessian,threeLogEnvelope_second p c hq,
    threeRadiusSq_second,threeRadiusSq_first,threeRadiusSq_first]
  simp only [threeRadiusSq_zero,hy,add_zero,mul_zero,zero_mul]
  field_simp [hx]
  ring

lemma threeLogEnvelope_gradient (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    coordinateMetricGradient (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0 =
      (c/(p.1:Euclidean 3) 0) • threeSphereDirection p 0 := by
  apply (selfMetricFlat_invertible (threeChartMetric threeBackgroundMetric p) 0).inverse_apply_eq.mpr
  rw [threeChartMetric_background_zero,threeLogEnvelope_first_axis p c hx hy]
lemma threeLogEnvelope_dual (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    (InnerProductSpace.toDual ℝ ThreeModel).symm (fderiv ℝ (threeLogEnvelope p c) 0) =
      (c/(p.1:Euclidean 3) 0) • threeSphereDirection p 0 := by
  rw [LinearIsometryEquiv.symm_apply_eq,threeLogEnvelope_first_axis p c hx hy]
  rfl
lemma threeLogEnvelope_trace (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0) :
    actualProfileTraceForm (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0
      (threeSphereDirection p 1) (threeSphereDirection p 1) =
      c*(1-c^2)*(1-((p.1:Euclidean 3) 0)^2)/((p.1:Euclidean 3) 0)^2 := by
  rw [actualProfileTraceForm,threeLogEnvelope_gradient p c hx hy,
    threeChartMetric_background_zero,metricProfileTraceForm_apply]
  simp only [ContinuousLinearMap.map_smul,smul_apply,smul_eq_mul]
  rw [threeLogEnvelope_hessian_axis p c hx hy,threeLogEnvelope_hessian_axis p c hx hy]
  have hi (v w : ThreeModel) : (innerSL ℝ v) w = inner ℝ v w := rfl
  simp only [hi,threeSphereDirection_inner,threeSphereDirection_fst_inner,hy]
  norm_num
  field_simp [hx]
  ring
lemma threeLogEnvelope_strict (p : ThreeManifold) (c : ℝ)
    (hx : (p.1:Euclidean 3) 0 ≠ 0) (hy : (p.1:Euclidean 3) 1=0)
    (hxlt : ((p.1:Euclidean 3) 0)^2<1) (hc : 0<c) (hc1 : c<1) :
    coordinateMetricGradient (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0 ≠ 0 ∧
    actualProfileStrict (threeChartMetric threeBackgroundMetric p) (threeLogEnvelope p c) 0 := by
  have hv0 : threeSphereDirection p 0 ≠ 0 := by
    intro hh
    have hi:=threeSphereDirection_inner p 0 0
    simp only [hh,inner_zero_left,ite_true] at hi
    nlinarith
  have he : threeSphereDirection p 1 ≠ 0 := by
    intro hh
    have hi:=threeSphereDirection_inner p 1 1
    simp [hh,hy] at hi
  constructor
  · rw [threeLogEnvelope_gradient p c hx hy]
    exact smul_ne_zero (div_ne_zero (ne_of_gt hc) hx) hv0
  · rw [actualProfileStrict,quadraticPlaneStrict_iff_nonzero]
    refine ⟨threeSphereDirection p 1,he,?_,?_⟩
    · rw [threeLogEnvelope_dual p c hx hy,real_inner_smul_left,threeSphereDirection_inner]
      norm_num [hy]
    · rw [threeLogEnvelope_trace p c hx hy]
      have hcc : 0<1-c^2 := by nlinarith
      exact div_pos (mul_pos (mul_pos hc hcc) (sub_pos.mpr hxlt)) (sq_pos_of_ne_zero hx)
end YauCounterexamples
end

end OAI
