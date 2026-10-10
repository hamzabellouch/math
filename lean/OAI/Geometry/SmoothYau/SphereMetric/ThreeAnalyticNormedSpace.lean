import Mathlib
import OAI.Geometry.SmoothYau.ProductMetric.ThreeInteriorMeridianNormedSpace

namespace OAI

noncomputable section
open Set Filter Function Manifold Module Metric
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeAnalyticNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeAnalyticContinuousSMul : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
local instance threeAnalytic_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma three_chart_sphere_analytic (p : ThreeManifold) :
    ContDiff ℝ ω (fun y : ThreeModel => (((chartAt ThreeModel p).symm y).1:Euclidean 3)) := by
  have he : (fun y : ThreeModel => (((chartAt ThreeModel p).symm y).1:Euclidean 3))=
      fun y => roundChart (p.1:Euclidean 3) (sphereFrame p.1) y.fst := by
    funext y
    exact congrArg (fun q : ThreeAmbient => q.fst) (congrFun (three_chart_symm p) y)
  rw [he]
  exact (contDiff_stereoInvFunAux.comp (sphereFrame p.1).toContinuousLinearMap.contDiff).comp
    (WithLp.fstL 2 ℝ (Euclidean 2) (Euclidean 1)).contDiff
lemma three_chart_circle_analytic (p : ThreeManifold) :
    ContDiff ℝ ω (fun y : ThreeModel => (((chartAt ThreeModel p).symm y).2:ℂ)) := by
  have he : (fun y : ThreeModel => (((chartAt ThreeModel p).symm y).2:ℂ))=
      fun y => roundChart (p.2:ℂ) (unitSphereFrame (n:=1) p.2) y.snd := by
    funext y
    exact congrArg (fun q : ThreeAmbient => q.snd) (congrFun (three_chart_symm p) y)
  rw [he]
  exact (contDiff_stereoInvFunAux.comp (unitSphereFrame (n:=1) p.2).toContinuousLinearMap.contDiff).comp
    (WithLp.sndL 2 ℝ (Euclidean 2) (Euclidean 1)).contDiff
lemma threeCoupled_chart_analytic (r : ℝ) (k : ℕ) (p : ThreeManifold) :
    ContDiff ℝ ω (threeCoupled r k ∘ (chartAt ThreeModel p).symm) := by
  have hA := (planarLinear (productAxis 0) (productAxis 1)).contDiff.comp (three_chart_sphere_analytic p)
  have hB := (planarLinear (productAxis 0) (productAxis 2)).contDiff.comp (three_chart_sphere_analytic p)
  have hz := three_chart_circle_analytic p
  exact Complex.reCLM.contDiff.comp (((hA.pow k).add (contDiff_const.mul (hB.pow k))).mul (hz.pow k))
lemma threeCoupled_gradient_chart_analytic (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : ThreeManifold) :
    ContDiff ℝ ω (coordinateGradientPair threeBackgroundMetric (threeCoupled r k) (threeCoupled r k) ∘
      (chartAt ThreeModel p).symm) := by
  have hA := (planarLinear (productAxis 0) (productAxis 1)).contDiff.comp (three_chart_sphere_analytic p)
  have hB := (planarLinear (productAxis 0) (productAxis 2)).contDiff.comp (three_chart_sphere_analytic p)
  have hz := three_chart_circle_analytic p
  have hα := (hz.pow k).mul (hA.pow (k-1))
  have hβ := ((hz.pow k).mul (contDiff_const (c:=(r:ℂ)^k))).mul (hB.pow (k-1))
  have hC := ((hA.pow k).add ((contDiff_const (c:=(r:ℂ)^k)).mul (hB.pow k))).mul (hz.pow k)
  have hu := threeCoupled_chart_analytic r k p
  have he : coordinateGradientPair threeBackgroundMetric (threeCoupled r k) (threeCoupled r k) ∘
      (chartAt ThreeModel p).symm = fun y =>
      (k:ℝ)^2*(((( ((chartAt ThreeModel p).symm y).2:ℂ)^k*productA ((chartAt ThreeModel p).symm y).1^(k-1)).re+
        ((((chartAt ThreeModel p).symm y).2:ℂ)^k*(r:ℂ)^k*productB ((chartAt ThreeModel p).symm y).1^(k-1)).re)^2+
        ((((chartAt ThreeModel p).symm y).2:ℂ)^k*productA ((chartAt ThreeModel p).symm y).1^(k-1)).im^2+
        ((((chartAt ThreeModel p).symm y).2:ℂ)^k*(r:ℂ)^k*productB ((chartAt ThreeModel p).symm y).1^(k-1)).im^2-
        (threeCoupled r k ((chartAt ThreeModel p).symm y))^2+
        (threeCoupledComplex r k ((chartAt ThreeModel p).symm y)).im^2) := by
    funext y; exact threeCoupled_gradient_value r k hk _
  rw [he]
  exact contDiff_const.mul (((((Complex.reCLM.contDiff.comp hα).add
    (Complex.reCLM.contDiff.comp hβ)).pow 2).add ((Complex.imCLM.contDiff.comp hα).pow 2)).add
    ((Complex.imCLM.contDiff.comp hβ).pow 2) |>.sub (hu.pow 2) |>.add ((Complex.imCLM.contDiff.comp hC).pow 2))
lemma threeInteriorMeridian_mem_profile_source (t : ℝ) :
    threeInteriorMeridian t ∈ (chartAt ThreeModel threeProfileCenter).source := by
  change threeInteriorMeridian t ∈ ((chartAt ThreeProductModel threeProfileCenter).trans
    threeModelEquiv.toHomeomorph.toOpenPartialHomeomorph).source
  simp only [OpenPartialHomeomorph.trans_source,Homeomorph.toOpenPartialHomeomorph_source,
    preimage_univ,inter_univ]
  change threeInteriorMeridian t ∈ (chartAt (Euclidean 2) threeProfileCenter.1).source ×ˢ
    (chartAt (Euclidean 1) threeProfileCenter.2).source
  constructor
  · change (threeInteriorMeridian t).1 ∈ (stereographic' 2 (-threeProfileCenter.1)).source
    rw [stereographic'_source]
    intro h
    have hh := congrArg (fun p : Sphere 2 => (p:Euclidean 3) 0) h
    norm_num [threeInteriorMeridian,threeInteriorMeridianAmbient,threeProfileCenter,
      threeProfilePoint,productAxis,PiLp.single_apply,Fin.ext_iff] at hh
  · change (1:Circle) ∈ (stereographic' 1 (-(1:Circle))).source
    erw [stereographic'_source]
    intro h
    have hh := congrArg (fun z : Circle => (z:ℂ).re) h
    norm_num at hh
end YauCounterexamples
end

end OAI
