import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.SphericalBaseProfileRadius

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def linearMetricForm (g : SmoothMetric E E) (L : F ≃L[ℝ] E) (x : F) : CoordinateForm F :=
  (selfMetricFlat g (L x)).bilinearComp L.toContinuousLinearMap L.toContinuousLinearMap
omit [FiniteDimensional ℝ E] in
lemma linearMetricForm_smooth (g : SmoothMetric E E) (L : F ≃L[ℝ] E) :
    ContDiff ℝ ∞ (linearMetricForm g L) := by
  apply contDiff_clm_apply_iff.mpr
  intro v
  apply contDiff_clm_apply_iff.mpr
  intro w
  exact (((contDiff_selfMetricFlat g).comp L.contDiff).clm_apply contDiff_const).clm_apply contDiff_const

def linearPullbackMetric (g : SmoothMetric E E) (L : F ≃L[ℝ] E) : SmoothMetric F F :=
  flatMetricOfForm (linearMetricForm g L) (linearMetricForm_smooth g L)
    (fun x v w => selfMetricFlat_symm g (L x) (L v) (L w))
    (fun x v hv => selfMetricFlat_pos g (L x) (by simpa using L.injective.ne hv))
omit [FiniteDimensional ℝ E] in
lemma linearPullbackMetric_flat (g : SmoothMetric E E) (L : F ≃L[ℝ] E) (x v w : F) :
    selfMetricFlat (linearPullbackMetric g L) x v w = selfMetricFlat g (L x) (L v) (L w) := by
  rw [selfMetricFlat_apply]
  rfl
omit [FiniteDimensional ℝ E] in
lemma linearPullbackMetric_first (g : SmoothMetric E E) (L : F ≃L[ℝ] E) (x v w z : F) :
    fderiv ℝ (selfMetricFlat (linearPullbackMetric g L)) x v w z =
      fderiv ℝ (selfMetricFlat g) (L x) (L v) (L w) (L z) := by
  rw [←fderiv_metric_pairing]
  simp_rw [linearPullbackMetric_flat]
  have hd : DifferentiableAt ℝ (fun y => selfMetricFlat g y (L w) (L z)) (L x) :=
    (((contDiff_selfMetricFlat g).clm_apply contDiff_const).clm_apply contDiff_const).differentiable (by simp) _
  change fderiv ℝ ((fun y => selfMetricFlat g y (L w) (L z)) ∘ L) x v = _
  rw [fderiv_comp x hd L.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply]
  exact fderiv_metric_pairing g (L x) (L v) (L w) (L z)
lemma linearPullbackMetric_Christoffel (g : SmoothMetric E E) (L : F ≃L[ℝ] E) (x v w : F) :
    L (metricChristoffel (linearPullbackMetric g L) x v w) =
      metricChristoffel g (L x) (L v) (L w) := by
  apply (selfMetricFlat_invertible g (L x)).injective
  ext z
  obtain ⟨z,rfl⟩ := L.surjective z
  rw [←linearPullbackMetric_flat,metricChristoffel_pairing,metricChristoffel_pairing]
  simp only [linearPullbackMetric_first]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma fderiv_linearEquiv_comp {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (L : F ≃L[ℝ] E) (x v : F) :
    fderiv ℝ (f ∘ L) x v = fderiv ℝ f (L x) (L v) := by
  rw [fderiv_comp x (hf.differentiable (by simp) _) L.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma second_linearEquiv_comp {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (L : F ≃L[ℝ] E) (x v w : F) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) x v w = fderiv ℝ (fderiv ℝ f) (L x) (L v) (L w) := by
  rw [←fderiv_fderiv_apply (hf.comp L.contDiff)]
  simp_rw [fderiv_linearEquiv_comp hf L]
  change fderiv ℝ ((fun y => fderiv ℝ f y (L w)) ∘ L) x v = _
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y (L w)) (L x) :=
    (((hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) _
  rw [fderiv_comp x hd L.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  exact fderiv_fderiv_apply hf (L x) (L v) (L w)
lemma linearPullbackMetric_hessian (g : SmoothMetric E E) (L : F ≃L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x v w : F) :
    actualCoordinateHessian (linearPullbackMetric g L) (f ∘ L) x v w =
      actualCoordinateHessian g f (L x) (L v) (L w) := by
  simp only [actualCoordinateHessian,coordinateCovariantSecond,sub_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply]
  rw [second_linearEquiv_comp hf L,fderiv_linearEquiv_comp hf L,linearPullbackMetric_Christoffel]
lemma linearPullbackMetric_gradient (g : SmoothMetric E E) (L : F ≃L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : F) :
    L (coordinateMetricGradient (linearPullbackMetric g L) (f ∘ L) x) =
      coordinateMetricGradient g f (L x) := by
  apply (selfMetricFlat_invertible g (L x)).injective
  ext z
  obtain ⟨z,rfl⟩ := L.surjective z
  rw [←linearPullbackMetric_flat]
  have h1 := (selfMetricFlat_invertible (linearPullbackMetric g L) x).inverse_apply_eq.mp
    (show (selfMetricFlat (linearPullbackMetric g L) x).inverse (fderiv ℝ (f ∘ L) x) =
      coordinateMetricGradient (linearPullbackMetric g L) (f ∘ L) x from rfl)
  have h2 := (selfMetricFlat_invertible g (L x)).inverse_apply_eq.mp
    (show (selfMetricFlat g (L x)).inverse (fderiv ℝ f (L x)) = coordinateMetricGradient g f (L x) from rfl)
  rw [←h1,←h2]
  exact fderiv_linearEquiv_comp hf L x z
end YauCounterexamples
end

end OAI
