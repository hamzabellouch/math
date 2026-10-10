import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ScalarLogFirst
import OAI.Geometry.SmoothYau.Geometry.ThreeDirectionsNormedSpace

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
local instance threeChartNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeChartContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul

def threeChartMetric (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold) :
    SmoothMetric ThreeModel ThreeModel :=
  flatMetricOfForm (chartMetricForm g p)
    (contDiffOn_univ.mp (by simpa only [three_chart_target] using chartMetricForm_contDiffOn g p))
    (chartMetricForm_symm g p)
    (fun y v hv => chartMetricForm_pos g p (by rw [three_chart_target]; trivial) hv)
lemma threeChartMetric_selfFlat (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold) (y : ThreeModel) :
    selfMetricFlat (threeChartMetric g p) y = chartMetricForm g p y := by
  ext v w
  rw [selfMetricFlat_apply]
  rfl
lemma threeChartMetric_background (p : ThreeManifold) (y v w : ThreeModel) :
    selfMetricFlat (threeChartMetric threeBackgroundMetric p) y v w =
      inner ℝ (fderiv ℝ (threeChartMap p) y v) (fderiv ℝ (threeChartMap p) y w) := by
  rw [threeChartMetric_selfFlat,chartMetricForm_pairing]
  change (inner ℝ : ThreeAmbient → ThreeAmbient → ℝ) (mfderiv 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ThreeAmbient) threeImmersion _ _) _ = _
  exact congrArg₂ (inner ℝ : ThreeAmbient → ThreeAmbient → ℝ) (three_coordinate_embedding p y v) (three_coordinate_embedding p y w)
lemma threeChartMetric_background_zero (p : ThreeManifold) :
    selfMetricFlat (threeChartMetric threeBackgroundMetric p) 0 = (innerSL ℝ : ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ) := by
  ext v w
  have hh : fderiv ℝ (threeChartMap p) 0 = (threeFrame p).toContinuousLinearMap :=
    (lpProductRoundChart_first (p.1:Euclidean 3) (p.2:ℂ) (sphereFrame p.1) (unitSphereFrame (n:=1) p.2)).fderiv
  rw [threeChartMetric_background,hh]
  exact (threeFrame p).inner_map_map _ _
lemma threeChartMetric_background_first (p : ThreeManifold) :
    fderiv ℝ (selfMetricFlat (threeChartMetric threeBackgroundMetric p)) 0 = 0 := by
  ext v w z
  rw [←fderiv_metric_pairing]
  simp_rw [threeChartMetric_background]
  exact congrArg (fun L : ThreeModel →L[ℝ] ℝ => L v)
    (lpProductRoundChart_metric_first (p.1:Euclidean 3) (p.2:ℂ)
      (sphereFrame p.1) (unitSphereFrame (n:=1) p.2)
      (sphereFrame_orthogonal p.1) (unitSphereFrame_orthogonal (n:=1) p.2) w z).fderiv
lemma threeChartMetric_background_Christoffel (p : ThreeManifold) :
    metricChristoffel (threeChartMetric threeBackgroundMetric p) 0 = 0 := by
  ext v w
  apply (selfMetricFlat_invertible (threeChartMetric threeBackgroundMetric p) 0).injective
  ext z
  rw [metricChristoffel_pairing,threeChartMetric_background_first]
  simp
lemma threeChartMetric_background_hessian (p : ThreeManifold) (f : ThreeModel → ℝ) :
    actualCoordinateHessian (threeChartMetric threeBackgroundMetric p) f 0 =
      fderiv ℝ (fderiv ℝ f) 0 := by
  simp [actualCoordinateHessian,coordinateCovariantSecond,threeChartMetric_background_Christoffel]
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
local instance threeRadiusNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeRadiusContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeRadiusEuclideanContinuousSMul (dimension : ℕ) : ContinuousSMul ℝ (Euclidean dimension) :=
  IsBoundedSMul.continuousSMul
local instance threeRadius_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩

def threeSphereMap (p : ThreeManifold) : ThreeModel → Euclidean 3 :=
  roundChart (p.1:Euclidean 3) (sphereFrame p.1) ∘ WithLp.fstL 2 ℝ (Euclidean 2) (Euclidean 1)
lemma threeSphereMap_smooth (p : ThreeManifold) : ContDiff ℝ ∞ (threeSphereMap p) :=
  (roundChart_smooth _ _).comp (WithLp.fstL 2 ℝ (Euclidean 2) (Euclidean 1)).contDiff
lemma threeSphereMap_zero (p : ThreeManifold) : threeSphereMap p 0 = (p.1 : Euclidean 3) := by
  simp [threeSphereMap,Function.comp_apply,roundChart_zero]
lemma threeSphereMap_first (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threeSphereMap p) 0 v = sphereFrame p.1 v.fst := by
  rw [threeSphereMap,directional_clm_comp_general _ ((roundChart_smooth _ _).differentiable (by simp))]
  change fderiv ℝ (roundChart (p.1:Euclidean 3) (sphereFrame p.1)) 0 v.fst = _
  rw [(roundChart_first _ _).fderiv]
  rfl
lemma threeSphereMap_second (p : ThreeManifold) (v w : ThreeModel) :
    fderiv ℝ (fderiv ℝ (threeSphereMap p)) 0 v w =
      -inner ℝ v.fst w.fst • (p.1:Euclidean 3) := by
  rw [←fderiv_fderiv_apply (threeSphereMap_smooth p)]
  rw [threeSphereMap,second_clm_comp_general _ (roundChart_smooth _ _)]
  change fderiv ℝ (fun y => fderiv ℝ (roundChart (p.1:Euclidean 3) (sphereFrame p.1)) y w.fst) 0 v.fst = _
  rw [(roundChart_second _ _ _).fderiv]
  simp [real_inner_comm,smul_neg,neg_smul]

def threeSphereCoord (p : ThreeManifold) (i : Fin 3) (y : ThreeModel) : ℝ :=
  inner ℝ (productAxis i) (threeSphereMap p y)
lemma threeSphereCoord_smooth (p : ThreeManifold) (i : Fin 3) :
    ContDiff ℝ ∞ (threeSphereCoord p i) := (innerSL ℝ (productAxis i)).contDiff.comp (threeSphereMap_smooth p)
lemma threeSphereCoord_zero (p : ThreeManifold) (i : Fin 3) :
    threeSphereCoord p i 0 = (p.1:Euclidean 3) i := by
  rw [threeSphereCoord,threeSphereMap_zero,productAxis_coord]
lemma threeSphereCoord_first (p : ThreeManifold) (i : Fin 3) (v : ThreeModel) :
    fderiv ℝ (threeSphereCoord p i) 0 v = inner ℝ (threeSphereDirection p i) v := by
  rw [show threeSphereCoord p i = fun y => (innerSL ℝ (productAxis i)) (threeSphereMap p y) from rfl]
  rw [fderiv_clm_comp_apply _ (threeSphereMap_smooth p),threeSphereMap_first]
  change inner ℝ (productAxis i) (unitSphereFrame (n:=2) p.1 v.fst)=_
  rw [real_inner_comm,unitSphereFrame_inner,real_inner_comm]
  simp [threeSphereDirection,WithLp.prod_inner_apply]
lemma threeSphereCoord_second (p : ThreeManifold) (i : Fin 3) (v w : ThreeModel) :
    fderiv ℝ (fderiv ℝ (threeSphereCoord p i)) 0 v w =
      -(p.1:Euclidean 3) i * inner ℝ v.fst w.fst := by
  rw [show threeSphereCoord p i = fun y => (innerSL ℝ (productAxis i)) (threeSphereMap p y) from rfl]
  rw [fderiv_second_clm_comp_apply _ (threeSphereMap_smooth p),threeSphereMap_second]
  simp [inner_smul_right,productAxis_coord,mul_comm]

def threeRadiusSq (p : ThreeManifold) (y : ThreeModel) : ℝ :=
  threeSphereCoord p 0 y^2+threeSphereCoord p 1 y^2
lemma threeRadiusSq_smooth (p : ThreeManifold) : ContDiff ℝ ∞ (threeRadiusSq p) :=
  ((threeSphereCoord_smooth p 0).pow 2).add ((threeSphereCoord_smooth p 1).pow 2)
lemma threeRadiusSq_zero (p : ThreeManifold) : threeRadiusSq p 0 =
    (p.1:Euclidean 3) 0^2+(p.1:Euclidean 3) 1^2 := by
  simp [threeRadiusSq,threeSphereCoord_zero]
lemma threeRadiusSq_first (p : ThreeManifold) (v : ThreeModel) :
    fderiv ℝ (threeRadiusSq p) 0 v =
      2*(p.1:Euclidean 3) 0*inner ℝ (threeSphereDirection p 0) v+
      2*(p.1:Euclidean 3) 1*inner ℝ (threeSphereDirection p 1) v := by
  have h0 := ((threeSphereCoord_smooth p 0).differentiable (by simp) (0:ThreeModel)).hasFDerivAt.pow 2
  have h1 := ((threeSphereCoord_smooth p 1).differentiable (by simp) (0:ThreeModel)).hasFDerivAt.pow 2
  have hh : HasFDerivAt (threeRadiusSq p) _ 0 := h0.add h1
  rw [hh.fderiv]
  simp [threeSphereCoord_zero,threeSphereCoord_first]
lemma threeRadiusSq_second (p : ThreeManifold) (v w : ThreeModel) :
    fderiv ℝ (fderiv ℝ (threeRadiusSq p)) 0 v w =
      2*(inner ℝ (threeSphereDirection p 0) v*inner ℝ (threeSphereDirection p 0) w+
        inner ℝ (threeSphereDirection p 1) v*inner ℝ (threeSphereDirection p 1) w)-
      2*threeRadiusSq p 0*inner ℝ v.fst w.fst := by
  rw [←threeChartMetric_background_hessian p]
  change actualCoordinateHessian (threeChartMetric threeBackgroundMetric p)
    (fun y => threeSphereCoord p 0 y^2+threeSphereCoord p 1 y^2) 0 v w = _
  rw [actualCoordinateHessian_add _ ((threeSphereCoord_smooth p 0).pow 2) ((threeSphereCoord_smooth p 1).pow 2)]
  rw [actualCoordinateHessian_square _ (threeSphereCoord_smooth p 0),actualCoordinateHessian_square _ (threeSphereCoord_smooth p 1)]
  rw [threeChartMetric_background_hessian,threeChartMetric_background_hessian,
    threeSphereCoord_first,threeSphereCoord_first,threeSphereCoord_first,threeSphereCoord_first,
    threeSphereCoord_second,threeSphereCoord_second,threeSphereCoord_zero,threeSphereCoord_zero,threeRadiusSq_zero]
  ring

end YauCounterexamples
end

end OAI
