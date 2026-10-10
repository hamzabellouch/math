import OAI.Geometry.RCD.Transport.LocalFeatureSpace
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OAI

/-! # The positive definite pairing supplied by local distance coordinates -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates.LocalQuadraticMidpointGeometry
variable {Y : Type*} [MetricSpace Y] [ProperSpace Y] {q : Y}
  (G : LocalQuadraticMidpointGeometry q)

theorem localInner_add_left (u v w : G.localFeatureSpace) :
    G.localInner (u+v) w = G.localInner u w+G.localInner v w := by
  dsimp only [localInner]
  change _ * (((u:ball q (1:ℝ)→ℝ) _ + (v:ball q (1:ℝ)→ℝ) _) -
    ((u:ball q (1:ℝ)→ℝ) _ + (v:ball q (1:ℝ)→ℝ) _)) = _
  ring

theorem localInner_smul_left (u v : G.localFeatureSpace) (c : ℝ) :
    G.localInner (c • u) v = c * G.localInner u v := by
  dsimp only [localInner]
  change _ * (c * (u:ball q (1:ℝ)→ℝ) _ - c * (u:ball q (1:ℝ)→ℝ) _) = _
  ring

theorem localInner_definite (u : G.localFeatureSpace) (hu : G.localInner u u = 0) : u = 0 := by
  have he := G.localInner_self u
  rw [hu] at he
  rcases mul_eq_zero.mp he.symm with hs | hd
  · have hs0 := sq_eq_zero_iff.mp hs
    apply Subtype.ext
    rw [(G.featureRepresentation u).eq_feature,hs0,zero_smul]
    rfl
  · have hd0 := sq_eq_zero_iff.mp hd
    have hxy : (G.featureRepresentation u).first = (G.featureRepresentation u).second :=
      Subtype.ext (dist_eq_zero.mp hd0)
    apply Subtype.ext
    rw [(G.featureRepresentation u).eq_feature,hxy,sub_self,smul_zero]
    rfl

@[instance_reducible] def localFeatureInnerCore : InnerProductSpace.Core ℝ G.localFeatureSpace where
  inner := G.localInner
  conj_inner_symm u v := by
    change G.localInner v u = G.localInner u v
    exact G.localInner_symm v u
  re_inner_nonneg u := by
    change 0 ≤ G.localInner u u
    rw [G.localInner_self]
    positivity
  add_left := G.localInner_add_left
  smul_left := G.localInner_smul_left
  definite := G.localInner_definite

def featureVector (x : closedBall q (1/4:ℝ)) : G.localFeatureSpace :=
  ⟨localDistanceFeature q x,mem_convexDifferenceSpace _ _ _ ⟨x,x.property,rfl⟩⟩

theorem localInner_featureVectors (x y : closedBall q (1/4:ℝ)) :
    G.localInner (G.featureVector x) (G.featureVector y) = quadraticDistanceFeature q x y := by
  let r := G.featureRepresentation (G.featureVector y)
  change r.scale * (quadraticDistanceFeature q x r.first-quadraticDistanceFeature q x r.second) = _
  rw [quadraticDistanceFeature_symm q (x:Y) (r.first:Y),
    quadraticDistanceFeature_symm q (x:Y) (r.second:Y)]
  have hh := G.representation_eval (G.featureVector y) (featureTestPoint x)
  change quadraticDistanceFeature q y x =
    r.scale * (quadraticDistanceFeature q r.first x-quadraticDistanceFeature q r.second x) at hh
  exact hh.symm.trans (quadraticDistanceFeature_symm q (y:Y) (x:Y))

end RegularPointCoordinates.LocalQuadraticMidpointGeometry

end

end OAI
