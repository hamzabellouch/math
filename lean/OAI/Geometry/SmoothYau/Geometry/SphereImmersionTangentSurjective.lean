import Mathlib
import OAI.Geometry.SmoothYau.Limits.PlanePairMap
import OAI.Geometry.SmoothYau.Smoothness.ActualCoordinateHessianApply

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
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
lemma sphere_immersion_tangent_surjective (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ v w : E, g.inner x v w = inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    {b : V} (hb : inner ℝ (F x) b = 0) : ∃ z : E, fderiv ℝ F x z = b := by
  obtain ⟨z,t,ht⟩ := sphere_immersion_spans g hF hg hn hd b
  have hzero : t = 0 := by
    have hh := congrArg (inner ℝ (F x)) ht
    rw [hb, inner_add_right, inner_smul_right, hn.self_of_nhds,
      sphere_immersion_normal_first hF hn z] at hh
    linarith
  exact ⟨z,by simpa [hzero] using ht.symm⟩

omit [FiniteDimensional ℝ E] in
theorem sphere_immersion_quadratic_two_plane (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ v w : E, g.inner x v w = inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (a b : V) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1)
    (hab : inner ℝ a b = 0) (hr : (inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2 < 1) :
    ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, (1-((inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2))*g.inner x v v ≤
        (inner ℝ a (fderiv ℝ F x v))^2+(inner ℝ b (fderiv ℝ F x v))^2 := by
  obtain ⟨za,hza⟩ := sphere_immersion_tangent_surjective g hF hg hn hd
    (projectedPlaneMap_tangent (F x) a b hn.self_of_nhds (1,0))
  obtain ⟨zb,hzb⟩ := sphere_immersion_tangent_surjective g hF hg hn hd
    (projectedPlaneMap_tangent (F x) a b hn.self_of_nhds (0,1))
  let S := planePairMap za zb
  have hS : ∀ c, fderiv ℝ F x (S c) = projectedPlaneMap (F x) a b c := by
    intro c
    change fderiv ℝ F x (c.1 • za+c.2 • zb) = _
    rw [map_add, map_smul, map_smul, hza, hzb]
    have he : c = c.1 • ((1,0) : ℝ × ℝ)+c.2 • ((0,1) : ℝ × ℝ) := by ext <;> simp
    conv_rhs => rw [he]
    rw [map_add, map_smul, map_smul]
  have hinj : Function.Injective S := by
    intro c d he
    apply projectedPlaneMap_injective (F x) a b hn.self_of_nhds ha hb hab hr
    rw [← hS, ← hS, he]
  refine ⟨LinearMap.range S, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj]
    simp
  · rintro _ ⟨c,rfl⟩
    rw [hg, hS]
    exact projectedPlaneMap_quadratic_lower (F x) a b hn.self_of_nhds ha hb hab c

theorem sphere_quadratic_hessian_margins (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E, g.inner y v w =
      inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (a b : V) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1)
    (hab : inner ℝ a b = 0) (C : ℝ)
    (hr : (inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2 ≤ 1/4) :
    let f := fun y => C+(inner ℝ a (F y))^2+(inner ℝ b (F y))^2
    (∀ v, -(1/2 : ℝ)*selfMetricFlat g x v v ≤ actualCoordinateHessian g f x v v) ∧
    (∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, selfMetricFlat g x v v ≤ actualCoordinateHessian g f x v v) := by
  intro f
  have hess := sphere_quadratic_profile_hessian g hF hg hn hd (innerSL ℝ a) (innerSL ℝ b) C
  simp only [innerSL_apply_apply] at hess
  have hpos : ∀ (v : E), 0 ≤ g.inner x v v := by
    intro v
    rw [hg.self_of_nhds v v]
    exact real_inner_self_nonneg
  have hr' : (inner ℝ a (F x))^2+(inner ℝ b (F x))^2 ≤ 1/4 := by
    simpa only [real_inner_comm a (F x), real_inner_comm b (F x)] using hr
  constructor
  · intro v
    dsimp only [f]
    rw [hess v v]
    rw [selfMetricFlat_apply]
    simp only [← sq]
    nlinarith [mul_le_mul_of_nonneg_right hr' (hpos v),
      sq_nonneg (inner ℝ a (fderiv ℝ F x v)), sq_nonneg (inner ℝ b (fderiv ℝ F x v))]
  · obtain ⟨P,hP,hbound⟩ := sphere_immersion_quadratic_two_plane g hF hg.self_of_nhds hn hd
      a b ha hb hab (by linarith)
    refine ⟨P,hP,?_⟩
    intro v hv
    have hh := hbound v hv
    dsimp only [f]
    rw [hess v v]
    rw [selfMetricFlat_apply]
    simp only [← sq]
    change g.inner x v v ≤
      2*((inner ℝ a (fderiv ℝ F x v))^2+(inner ℝ b (fderiv ℝ F x v))^2)-
      2*((inner ℝ a (F x))^2+(inner ℝ b (F x))^2)*g.inner x v v
    rw [real_inner_comm a (F x), real_inner_comm b (F x)] at hh
    nlinarith [mul_le_mul_of_nonneg_right hr' (hpos v)]

theorem sphere_quadratic_hessian_margins_strong (g : SmoothMetric E E) {F : E → V}
    (hF : ContDiff ℝ ∞ F) {x : E}
    (hg : ∀ᶠ y in 𝓝 x, ∀ v w : E, g.inner y v w =
      inner ℝ (fderiv ℝ F y v) (fderiv ℝ F y w))
    (hn : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hd : Module.finrank ℝ V = Module.finrank ℝ E + 1)
    (a b : V) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1)
    (hab : inner ℝ a b = 0) (C : ℝ)
    (hr : (inner ℝ (F x) a)^2+(inner ℝ (F x) b)^2 ≤ 1/8) :
    let f := fun y => C+(inner ℝ a (F y))^2+(inner ℝ b (F y))^2
    (∀ v, -(1/4 : ℝ)*selfMetricFlat g x v v ≤ actualCoordinateHessian g f x v v) ∧
    (∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, (3/2 : ℝ)*selfMetricFlat g x v v ≤ actualCoordinateHessian g f x v v) := by
  intro f
  have hess := sphere_quadratic_profile_hessian g hF hg hn hd (innerSL ℝ a) (innerSL ℝ b) C
  simp only [innerSL_apply_apply] at hess
  have hpos : ∀ (v : E), 0 ≤ g.inner x v v := by
    intro v
    rw [hg.self_of_nhds v v]
    exact real_inner_self_nonneg
  have hr' : (inner ℝ a (F x))^2+(inner ℝ b (F x))^2 ≤ 1/8 := by
    simpa only [real_inner_comm a (F x), real_inner_comm b (F x)] using hr
  constructor
  · intro v
    dsimp only [f]
    rw [hess v v]
    rw [selfMetricFlat_apply]
    simp only [← sq]
    nlinarith [mul_le_mul_of_nonneg_right hr' (hpos v),
      sq_nonneg (inner ℝ a (fderiv ℝ F x v)), sq_nonneg (inner ℝ b (fderiv ℝ F x v))]
  · obtain ⟨P,hP,hbound⟩ := sphere_immersion_quadratic_two_plane g hF hg.self_of_nhds hn hd
      a b ha hb hab (by linarith)
    refine ⟨P,hP,?_⟩
    intro v hv
    have hh := hbound v hv
    dsimp only [f]
    rw [hess v v]
    rw [selfMetricFlat_apply]
    simp only [← sq]
    change (3/2 : ℝ)*g.inner x v v ≤
      2*((inner ℝ a (fderiv ℝ F x v))^2+(inner ℝ b (fderiv ℝ F x v))^2)-
      2*((inner ℝ a (F x))^2+(inner ℝ b (F x))^2)*g.inner x v v
    rw [real_inner_comm a (F x), real_inner_comm b (F x)] at hh
    nlinarith [mul_le_mul_of_nonneg_right hr' (hpos v)]

end YauCounterexamples

end

end OAI
