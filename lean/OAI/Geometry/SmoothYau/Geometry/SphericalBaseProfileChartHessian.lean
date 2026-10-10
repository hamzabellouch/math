import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContinuousCompactSmoothJets

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma twoPlane_has_transverse (hd : Module.finrank ℝ E = 3)
    (P : Submodule ℝ E) (hP : Module.finrank ℝ P = 2) (q : E) :
    ∃ v : E, v ∈ P ∧ v ≠ 0 ∧ inner ℝ q v = 0 := by
  by_cases hq : q = 0
  · obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0 < Module.finrank ℝ P by omega)
    exact ⟨v,v.property,(fun h => hv (Subtype.ext h)),by simp [hq]⟩
  let K := (ℝ ∙ q)ᗮ
  let : Fact (Module.finrank ℝ E = 2+1) := ⟨hd⟩
  have hK : Module.finrank ℝ K = 2 := Submodule.finrank_orthogonal_span_singleton hq
  have hi := P.finrank_sup_add_finrank_inf_eq K
  have hu : Module.finrank ℝ (P ⊔ K : Submodule ℝ E) ≤ 3 :=
    (Submodule.finrank_le _).trans_eq hd
  obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℝ (P ⊓ K : Submodule ℝ E) by omega)
  exact ⟨v,v.property.1,(fun h => hv (Subtype.ext h)),
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property.2⟩

theorem metricProfileStrict_of_two_plane (hd : Module.finrank ℝ E = 3)
    (B H : CoordinateForm E) (a q : E)
    (hB : ∀ v, v ≠ 0 → 0 < B v v)
    (hlower : ∀ v, -(1/2 : ℝ)*B v v ≤ H v v)
    (hplane : ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, B v v ≤ H v v) :
    quadraticPlaneStrict (metricProfileTraceForm B H a) q := by
  obtain ⟨P,hP,hpos⟩ := hplane
  obtain ⟨v,hvP,hv,hq⟩ := twoPlane_has_transverse hd P hP q
  rw [quadraticPlaneStrict_iff_nonzero]
  refine ⟨v,hv,hq,?_⟩
  rw [metricProfileTraceForm_apply]
  have hvpos := hB v hv
  have hapos : 0 ≤ B a a := by
    by_cases ha : a = 0
    · simp [ha]
    · exact (hB a ha).le
  have h₁ := mul_le_mul_of_nonneg_left (hlower a) hvpos.le
  have h₂ := mul_le_mul_of_nonneg_left (hpos v hvP) (by linarith : 0 ≤ 1+B a a)
  nlinarith [mul_nonneg hvpos.le hapos]

theorem actualProfileStrict_of_two_plane (g : SmoothMetric E E)
    (hd : Module.finrank ℝ E = 3) (f : E → ℝ) (x : E)
    (hlower : ∀ v, -(1/2 : ℝ)*selfMetricFlat g x v v ≤ actualCoordinateHessian g f x v v)
    (hplane : ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, selfMetricFlat g x v v ≤ actualCoordinateHessian g f x v v) :
    actualProfileStrict g f x :=
  metricProfileStrict_of_two_plane hd _ _ _ _ (fun v hv => selfMetricFlat_pos g x (v := v) hv) hlower hplane


end

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
open Set Filter Manifold
open scoped Topology ContDiff

lemma sphericalBaseProfile_chart_hessian_param
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (p : Sphere 3)
    (a b : Euclidean 4) (s t : ℝ) (y : Euclidean 3) :
    actualCoordinateHessian (sphereChartMetric g p)
      (sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm) y =
    actualCoordinateHessian (sphereChartMetric g p)
      (sphericalBaseProfile a b s ∘ (chartAt (Euclidean 3) p).symm) y := by
  have he : sphericalBaseProfile a b t ∘ (chartAt (Euclidean 3) p).symm =
      fun z => (Real.log t-t^2-(Real.log s-s^2)) +
        (sphericalBaseProfile a b s ∘ (chartAt (Euclidean 3) p).symm) z := by
    funext z
    dsimp [sphericalBaseProfile,Function.comp_def]
    ring
  rw [he]
  ext v w
  rw [actualCoordinateHessian_add _ contDiff_const (sphericalBaseProfile_chart_smooth p a b s),
    actualCoordinateHessian_const,zero_add]

lemma sphericalRadius_chart_sq (p : Sphere 3) (a b : Euclidean 4) (y : Euclidean 3) :
    (sphericalRadius a b ((chartAt (Euclidean 3) p).symm y))^2 =
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) a)^2 +
      (inner ℝ (roundChart (p : Euclidean 4) (sphereFrame p) y) b)^2 := by
  rw [sphericalRadius_sq,congrFun (sphere_chart_symm p) y]
  rw [real_inner_comm a,real_inner_comm b]

theorem sphericalBaseProfile_uniform_neighborhood
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀) :
    IsSmoothNeighborhood g₀ {g | ∀ t : ℝ, ∀ y ∈
      sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      hessianMargins (selfMetricFlat (sphereChartMetric g sourcePole) y)
        (actualCoordinateHessian (sphereChartMetric g sourcePole)
          (sphericalBaseProfile sourceAxisOne sourceAxisTwo t ∘
            (chartAt (Euclidean 3) sourcePole).symm) y)} := by
  obtain ⟨ha,hb,hab⟩ := source_axes_orthonormal
  have hK := sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo
    sphericalRadius_neg_sourcePole (R := 3/10) (by norm_num)
  have hr : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      (inner ℝ (roundChart (sourcePole : Euclidean 4) (sphereFrame sourcePole) y) sourceAxisOne)^2 +
      (inner ℝ (roundChart (sourcePole : Euclidean 4) (sphereFrame sourcePole) y) sourceAxisTwo)^2
        ≤ 1/8 := by
    intro y hy
    have hb := (mem_sphericalCoverage_iff sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole (R := 3/10) (by norm_num) y).mp hy
    rw [← sphericalRadius_chart_sq]
    have hn := sphericalRadius_nonneg sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y)
    nlinarith
  obtain ⟨tests,ε,hε,htests⟩ := sphericalBaseProfile_neighborhood g₀ hg₀ sourcePole
    sourceAxisOne sourceAxisTwo ha hb hab 0 hK hr
  refine ⟨tests,ε,hε,?_⟩
  intro g hg t y hy
  rw [sphericalBaseProfile_chart_hessian_param g sourcePole sourceAxisOne sourceAxisTwo 0 t]
  exact htests g hg y hy

lemma hessianMargins_actualProfileStrict (g : SmoothMetric (Euclidean 3) (Euclidean 3))
    (f : Euclidean 3 → ℝ) (y : Euclidean 3)
    (h : hessianMargins (selfMetricFlat g y) (actualCoordinateHessian g f y)) :
    actualProfileStrict g f y :=
  actualProfileStrict_of_two_plane g (by simp [Euclidean]) f y
    (hessianMargins_lower h) (hessianMargins_plane h)

lemma hessianMargins_positive_two_plane (g : SmoothMetric (Euclidean 3) (Euclidean 3))
    (f : Euclidean 3 → ℝ) (y : Euclidean 3)
    (h : hessianMargins (selfMetricFlat g y) (actualCoordinateHessian g f y)) :
    ∃ P : Submodule ℝ (Euclidean 3), Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g f y v v := by
  obtain ⟨P,hP,hp⟩ := hessianMargins_plane h
  exact ⟨P,hP,fun v hv hv0 => (selfMetricFlat_pos g y hv0).trans_le (hp v hv)⟩



end YauCounterexamples
end

end OAI
