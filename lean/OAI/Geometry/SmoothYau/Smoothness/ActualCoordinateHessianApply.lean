import Mathlib
import OAI.Geometry.SmoothYau.Estimates.SphereImmersionSpans

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
section ScalarHessian
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma actualCoordinateHessian_apply (g : SmoothMetric E E) (f : E → ℝ) (x v w : E) :
    actualCoordinateHessian g f x v w =
      fderiv ℝ (fderiv ℝ f) x v w - fderiv ℝ f x (metricChristoffel g x v w) := by
  rfl

omit [FiniteDimensional ℝ E] in
lemma fderiv_clm_comp_apply (L : V →L[ℝ] ℝ) {F : E → V}
    (hF : ContDiff ℝ ∞ F) (x v : E) :
    fderiv ℝ (fun y => L (F y)) x v = L (fderiv ℝ F x v) := by
  change (fderiv ℝ (L ∘ F) x) v = _
  rw [(L.hasFDerivAt.comp x ((hF.differentiable (by simp) x).hasFDerivAt)).fderiv]
  rfl

omit [FiniteDimensional ℝ E] in
lemma fderiv_second_clm_comp_apply (L : V →L[ℝ] ℝ) {F : E → V}
    (hF : ContDiff ℝ ∞ F) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => L (F y))) x v w =
      L (fderiv ℝ (fderiv ℝ F) x v w) := by
  have hLF : ContDiff ℝ ∞ (fun y => L (F y)) := L.contDiff.comp hF
  rw [← fderiv_fderiv_apply hLF]
  simp_rw [fderiv_clm_comp_apply L hF]
  rw [fderiv_clm_comp_apply L
    ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const),
    fderiv_fderiv_apply hF]

lemma actualCoordinateHessian_add (g : SmoothMetric E E) {f h : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (x v w : E) :
    actualCoordinateHessian g (fun y => f y + h y) x v w =
      actualCoordinateHessian g f x v w + actualCoordinateHessian g h x v w := by
  have hfd := hf.differentiable (by simp)
  have hhd := hh.differentiable (by simp)
  simp only [actualCoordinateHessian_apply]
  have he : fderiv ℝ (fun y => f y + h y) =
      fun y => fderiv ℝ f y + fderiv ℝ h y := by
    funext y
    exact fderiv_add (hfd y) (hhd y)
  rw [he, fderiv_fun_add
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    ((hh.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)]
  simp only [add_apply]
  ring

lemma actualCoordinateHessian_const (g : SmoothMetric E E) (c : ℝ) (x v w : E) :
    actualCoordinateHessian g (fun _ => c) x v w = 0 := by
  simp [actualCoordinateHessian_apply, fderiv_const_apply]

lemma actualCoordinateHessian_square (g : SmoothMetric E E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    actualCoordinateHessian g (fun y => (f y)^2) x v w =
      2 * (fderiv ℝ f x v) * (fderiv ℝ f x w) +
      2 * f x * actualCoordinateHessian g f x v w := by
  have hfd := hf.differentiable (by simp)
  have hff : ContDiff ℝ ∞ (fun y => (f y)^2) := hf.pow 2
  have he (y z : E) : fderiv ℝ (fun s => (f s)^2) y z =
      2 * f y * fderiv ℝ f y z := by
    simp only [pow_two]
    rw [fderiv_fun_mul (hfd y) (hfd y)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [actualCoordinateHessian_apply, ← fderiv_fderiv_apply hff]
  simp_rw [he]
  have hdf : ContDiff ℝ ∞ (fun y => fderiv ℝ f y w) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [fderiv_fun_mul ((contDiff_const.mul hf).differentiable (by simp) x)
      (hdf.differentiable (by simp) x),
    fderiv_fun_mul (differentiableAt_const _) (hfd x)]
  simp only [add_apply, smul_apply, smul_eq_mul, fderiv_const_apply, zero_apply]
  rw [fderiv_fderiv_apply hf, actualCoordinateHessian_apply]
  ring

end ScalarHessian
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem sphere_coordinate_hessian (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      g.inner y v w = inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (L : V →L[ℝ] ℝ) (v w : E) :
    actualCoordinateHessian g (fun y => L (F y)) x v w =
      -L (F x) * selfMetricFlat g x v w := by
  rw [actualCoordinateHessian_apply, fderiv_clm_comp_apply L hF,
    fderiv_second_clm_comp_apply L hF, ← map_sub]
  rw [sphere_immersion_gauss g hF hg hn
    (sphere_immersion_spans g hF hg.self_of_nhds hn hd)]
  simp only [map_smul, smul_eq_mul]
  ring

theorem sphere_quadratic_profile_hessian (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      g.inner y v w = inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (L₁ L₂ : V →L[ℝ] ℝ) (c : ℝ) (v w : E) :
    actualCoordinateHessian g (fun y => c + (L₁ (F y))^2 + (L₂ (F y))^2) x v w =
      2 * (L₁ (fderiv ℝ F x v) * L₁ (fderiv ℝ F x w) +
        L₂ (fderiv ℝ F x v) * L₂ (fderiv ℝ F x w)) -
      2 * ((L₁ (F x))^2 + (L₂ (F x))^2) * selfMetricFlat g x v w := by
  have h₁ : ContDiff ℝ ∞ (fun y => L₁ (F y)) := L₁.contDiff.comp hF
  have h₂ : ContDiff ℝ ∞ (fun y => L₂ (F y)) := L₂.contDiff.comp hF
  rw [actualCoordinateHessian_add g (contDiff_const.add (h₁.pow 2)) (h₂.pow 2),
    actualCoordinateHessian_add g contDiff_const (h₁.pow 2),
    actualCoordinateHessian_const, actualCoordinateHessian_square g h₁,
    actualCoordinateHessian_square g h₂,
    sphere_coordinate_hessian g hF hg hn hd L₁,
    sphere_coordinate_hessian g hF hg hn hd L₂]
  simp only [fderiv_clm_comp_apply L₁ hF, fderiv_clm_comp_apply L₂ hF]
  ring

end YauCounterexamples

end

end OAI
