import OAI.Geometry.RCD.Transport.LocalQuadraticMidpointGeometry
import OAI.Geometry.RCD.Harmonic.QuadraticDistanceFeature

namespace OAI

/-! # Squared-distance coordinates of the local midpoint geometry -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates.LocalQuadraticMidpointGeometry
variable {Y : Type*} [MetricSpace Y] {q : Y} (G : LocalQuadraticMidpointGeometry q)

abbrev feature (x : ball q (1/2:ℝ)) : ball q (1:ℝ) → ℝ :=
  fun z => quadraticDistanceFeature q x z

private theorem in_large (x : ball q (1/2:ℝ)) : (x:Y) ∈ ball q (1:ℝ) :=
  x.property.trans (by norm_num : (1/2:ℝ)<1)

omit G in
theorem feature_injective : Function.Injective (feature (q:=q)) := by
  intro x y h
  have hx := congrFun h ⟨x,in_large x⟩
  have hy := congrFun h ⟨y,in_large y⟩
  change quadraticDistanceFeature q x x = quadraticDistanceFeature q y x at hx
  change quadraticDistanceFeature q x y = quadraticDistanceFeature q y y at hy
  simp only [quadraticDistanceFeature,dist_self,zero_pow (by norm_num : 2≠0),sub_zero] at hx hy
  rw [dist_comm (y:Y) (x:Y)] at hx
  apply Subtype.ext
  apply dist_eq_zero.mp
  apply sq_eq_zero_iff.mp
  nlinarith only [hx,hy]

omit G in
theorem feature_continuous : Continuous (feature (q:=q)) := by
  apply continuous_pi
  intro z
  dsimp only [feature,quadraticDistanceFeature]
  exact ((((continuous_const.dist continuous_subtype_val).pow 2).add continuous_const).sub
    ((continuous_subtype_val.dist continuous_const).pow 2)).div_const 2

theorem feature_mid (x y : ball q (1/2:ℝ)) :
    feature (G.mid x y) = (1/2:ℝ) • (feature x + feature y) := by
  funext z
  have hq := G.quadratic x y q (by simp)
  have hz := G.quadratic x y z z.property
  dsimp only [feature,quadraticDistanceFeature,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  rw [dist_comm (G.mid x y:Y) (z:Y),hq,hz]
  rw [dist_comm (x:Y) (z:Y),dist_comm (y:Y) (z:Y)]
  ring

omit G in
@[simp] theorem feature_center : feature (q:=q) ⟨q,by simp⟩ = 0 := by
  funext z
  exact congrFun (quadraticDistanceFeature_self q) z

theorem feature_half (x : ball q (1/2:ℝ)) :
    feature (G.mid ⟨q,by simp⟩ x) = (1/2:ℝ) • feature x := by
  rw [G.feature_mid,feature_center,zero_add]

theorem mid_medial (w x y z : ball q (1/2:ℝ)) :
    G.mid (G.mid w x) (G.mid y z) = G.mid (G.mid w y) (G.mid x z) := by
  apply feature_injective
  simp only [G.feature_mid]
  funext a
  simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  ring

end RegularPointCoordinates.LocalQuadraticMidpointGeometry

end

end OAI
