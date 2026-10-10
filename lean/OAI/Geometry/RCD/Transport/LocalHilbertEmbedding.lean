import OAI.Geometry.RCD.Transport.LocalFeatureInner
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! # A genuine inner-product realization of the local midpoint geometry -/

open Set Metric
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates.LocalQuadraticMidpointGeometry
universe u
variable {Y : Type u} [MetricSpace Y] [ProperSpace Y] {q : Y}
  (G : LocalQuadraticMidpointGeometry q)

include G in
theorem exists_local_inner_product_embedding :
    ∃ (E : Type u) (m : NormedAddCommGroup E),
      letI := m
      ∃ (_ : InnerProductSpace ℝ E) (f : closedBall q (1/4:ℝ) → E),
        Isometry f ∧ Convex ℝ (range f) ∧ IsCompact (range f) ∧
          Submodule.span ℝ (range f) = ⊤ ∧ f ⟨q,by simp⟩ = 0 := by
  let E := G.localFeatureSpace
  let : InnerProductSpace.Core ℝ E := G.localFeatureInnerCore
  let : NormedAddCommGroup E := InnerProductSpace.Core.toNormedAddCommGroup (𝕜:=ℝ)
  let : InnerProductSpace ℝ E := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℝ E)
  let : TopologicalSpace E :=
    (inferInstance : NormedAddCommGroup E).toMetricSpace.toUniformSpace.toTopologicalSpace
  let f : closedBall q (1/4:ℝ) → E := G.featureVector
  have hinner (x y : closedBall q (1/4:ℝ)) :
      ⟪f x,f y⟫_ℝ = quadraticDistanceFeature q x y := G.localInner_featureVectors x y
  have hiso : Isometry f := by
    apply Isometry.of_dist_eq
    intro x y
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [dist_eq_norm,norm_sub_sq_real,← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq,hinner,hinner,hinner]
    simp only [quadraticDistanceFeature,dist_self,zero_pow (by norm_num : 2≠0)]
    change _ = dist (x:Y) (y:Y)^2
    ring
  have hconvex : Convex ℝ (range f) := by
    apply convex_iff_add_mem.mpr
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ a b ha hb hab
    have hc := G.convex_local_feature_image (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1/2)
    obtain ⟨z,hz,he⟩ := hc ⟨x,x.property,rfl⟩ ⟨y,y.property,rfl⟩ ha hb hab
    exact ⟨⟨z,hz⟩,Subtype.ext he⟩
  have hcompact : IsCompact (range f) := by
    simpa only [image_univ] using isCompact_univ.image hiso.continuous
  have hspan : Submodule.span ℝ (range f) = ⊤ := by
    apply top_unique
    intro u _
    let w := G.featureRepresentation u
    have he : u = w.scale • (f w.first-f w.second) := Subtype.ext w.eq_feature
    rw [he]
    apply Submodule.smul_mem
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨w.first,rfl⟩)
      (Submodule.subset_span ⟨w.second,rfl⟩)
  have hzero : f ⟨q,by simp⟩ = 0 := by
    apply Subtype.ext
    funext z
    exact congrFun (quadraticDistanceFeature_self q) z
  exact ⟨E,inferInstance,inferInstance,f,hiso,hconvex,hcompact,hspan,hzero⟩

end RegularPointCoordinates.LocalQuadraticMidpointGeometry

end

end OAI
