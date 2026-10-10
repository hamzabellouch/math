import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.PulledGradient

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
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [FiniteDimensional ℝ E] in
lemma fderiv_metric_pairing (g : SmoothMetric E E) (x v w z : E) :
    fderiv ℝ (fun y => selfMetricFlat g y w z) x v =
      fderiv ℝ (selfMetricFlat g) x v w z := by
  have hd := (contDiff_selfMetricFlat g).differentiable (by simp)
  rw [fderiv_clm_apply ((hd x).clm_apply (differentiableAt_const w))
      (differentiableAt_const z), fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simp

omit [FiniteDimensional ℝ E] in
lemma fderiv_fderiv_apply {F : E → V} (hF : ContDiff ℝ ∞ F) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ F y w) x v = fderiv ℝ (fderiv ℝ F) x v w := by
  rw [fderiv_clm_apply ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const w)]
  simp

omit [FiniteDimensional ℝ E] in
lemma fderiv_induced_metric (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      g.inner y v w = inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w)) (v w z : E) :
    fderiv ℝ (selfMetricFlat g) x v w z =
      inner ℝ (fderiv ℝ (fderiv ℝ F) x v w) (fderiv ℝ F x z) +
      inner ℝ (fderiv ℝ F x w) (fderiv ℝ (fderiv ℝ F) x v z) := by
  have he : (fun y => selfMetricFlat g y w z) =ᶠ[𝓝 x]
      (fun y => inner ℝ (fderiv ℝ F y w) (fderiv ℝ F y z)) := by
    filter_upwards [hg] with y hy
    exact hy w z
  rw [← fderiv_metric_pairing, he.fderiv_eq]
  have hd := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  rw [fderiv_inner_apply _ ((hd x).clm_apply (differentiableAt_const w))
      ((hd x).clm_apply (differentiableAt_const z)),
    fderiv_fderiv_apply hF, fderiv_fderiv_apply hF]
  ring

lemma induced_metric_christoffel (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      g.inner y v w = inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w)) (v w z : E) :
    inner ℝ (fderiv ℝ F x (metricChristoffel g x v w)) (fderiv ℝ F x z) =
      inner ℝ (fderiv ℝ (fderiv ℝ F) x v w) (fderiv ℝ F x z) := by
  have hgx := hg.self_of_nhds
  rw [← hgx, ← selfMetricFlat_apply, metricChristoffel_pairing]
  simp only [fderiv_induced_metric g hF hg]
  have hs : IsSymmSndFDerivAt ℝ F x := hF.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))
  rw [hs w v, hs z v, hs z w,
    real_inner_comm (fderiv ℝ F x w) (fderiv ℝ (fderiv ℝ F) x v z)]
  ring

omit [FiniteDimensional ℝ E] in
lemma sphere_immersion_normal_first {F : E → V} (hF : ContDiff ℝ ∞ F) {x : E}
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1) (v : E) :
    inner ℝ (F x) (fderiv ℝ F x v) = 0 := by
  have he : (fun y => inner ℝ (F y) (F y)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := hn
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) he.fderiv_eq
  have hd := hF.differentiable (by simp) x
  rw [fderiv_inner_apply ℝ hd hd] at hh
  simp only [fderiv_const_apply, zero_apply,
    real_inner_comm (F x)] at hh
  linarith

omit [FiniteDimensional ℝ E] in
lemma sphere_immersion_normal_second {F : E → V} (hF : ContDiff ℝ ∞ F) {x : E}
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1) (v w : E) :
    inner ℝ (F x) (fderiv ℝ (fderiv ℝ F) x v w) =
      -inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  have he : (fun y => inner ℝ (F y) (fderiv ℝ F y w)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_eventually_nhds.2 hn] with y hy
    exact sphere_immersion_normal_first hF hy w
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) he.fderiv_eq
  have hd := hF.differentiable (by simp) x
  have hdd := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_inner_apply ℝ hd (hdd.clm_apply (differentiableAt_const w)),
    fderiv_fderiv_apply hF] at hh
  simp only [fderiv_const_apply, zero_apply] at hh
  linarith

theorem sphere_immersion_gauss (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E,
      g.inner y v w = inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hspan : ∀ b : V, ∃ z : E, ∃ t : ℝ, b = fderiv ℝ F x z + t • F x)
    (v w : E) :
    fderiv ℝ (fderiv ℝ F) x v w - fderiv ℝ F x (metricChristoffel g x v w) =
      -(selfMetricFlat g x v w) • F x := by
  apply ext_inner_right ℝ
  intro b
  obtain ⟨z,t,rfl⟩ := hspan b
  have hfirst (a : E) : inner ℝ (fderiv ℝ F x a) (F x) = 0 := by
    rw [real_inner_comm]
    exact sphere_immersion_normal_first hF hn a
  have hsecond : inner ℝ (fderiv ℝ (fderiv ℝ F) x v w) (F x) =
      -selfMetricFlat g x v w := by
    rw [real_inner_comm, sphere_immersion_normal_second hF hn,
      ← hg.self_of_nhds v w]
    rfl
  simp only [inner_add_right, inner_smul_right, inner_sub_left, real_inner_smul_left]
  rw [induced_metric_christoffel g hF hg, hfirst, hsecond,
    sphere_immersion_normal_first hF hn, hn.self_of_nhds]
  ring

end YauCounterexamples

end

end OAI
