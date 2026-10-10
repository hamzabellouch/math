import Mathlib
import OAI.Geometry.HyperbolicGroups.LocalGeodesicCover
import OAI.Geometry.HyperbolicGroups.LocalGeodesicContraction

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {E X : Type*} [MetricSpace E] [MetricSpace X]

lemma UniformMetricCoverData.small_ball_pathConnected {p : E → X} {r : ℝ}
    (h : UniformMetricCoverData p r) (g : IsGeodesic X)
    (a : E) {ε : ℝ} (hε : 0<ε) (hεr : ε<r/4) : IsPathConnected (ball a ε) := by
  refine ⟨a,mem_ball_self hε,?_⟩
  intro b hb
  have hab : dist a b<ε := by simpa [mem_ball,dist_comm] using hb
  have hpab : dist (p a) (p b)=dist a b := h.local_dist a b (by linarith [h.positive])
  let γ:=g.segment (p a) (p b)
  have hγ:=g.segment_spec (p a) (p b)
  have hm (t : I) : γ t ∈ ball (p a) (r/4) := by
    rw [mem_ball,dist_comm,hγ.dist_from_source t.property,hpab]
    have hh : (t:ℝ)*dist a b≤dist a b := by nlinarith [t.property.2,dist_nonneg (x:=a) (y:=b)]
    exact hh.trans_lt (hab.trans hεr)
  let f : I → E := fun t => (h.out (p a) ⟨a,rfl⟩ ⟨γ t,hm t⟩).val
  have hf : Continuous f := continuous_subtype_val.comp ((h.out_isometry (p a) ⟨a,rfl⟩).continuous.comp
    ((continuousOn_iff_continuous_domRestrict.mp hγ.continuousOn).subtype_mk hm))
  have hd (t : I) : dist (f t) a=(t:ℝ)*dist a b := by
    rw [show dist (f t) a=dist (γ t) (p a) from h.out_dist _ _ _,dist_comm,hγ.dist_from_source t.property,hpab]
  have h0 : f 0=a := by apply dist_eq_zero.mp; rw [hd]; simp
  have h1 : f 1=b := by
    apply h.nearby_unique
    · have hh:=dist_triangle (f 1) a b
      rw [hd] at hh
      norm_num at hh
      linarith [h.positive]
    · exact (h.out_proj _ _ _).trans hγ.2.1
  refine ⟨⟨⟨f,hf⟩,h0,h1⟩,fun t => ?_⟩
  change dist (f t) a<ε
  rw [hd]
  nlinarith [t.property.2,dist_nonneg (x:=a) (y:=b)]

lemma UniformMetricCoverData.locallyPathConnected {p : E → X} {r : ℝ}
    (h : UniformMetricCoverData p r) (g : IsGeodesic X) : LocallyPathConnectedSpace E := by
  apply LocallyPathConnectedSpace.of_bases (p:=fun _ ε => 0<ε ∧ ε<r/4) (s:=fun a ε => ball a ε)
  · intro a
    apply Metric.nhds_basis_ball.to_hasBasis
    · intro ε hε
      refine ⟨min ε (r/8),⟨lt_min hε (by linarith [h.positive]),?_⟩,ball_subset_ball (min_le_left _ _)⟩
      exact (min_le_right _ _).trans_lt (by linarith [h.positive])
    · intro ε hε
      exact ⟨ε,hε.1,Subset.rfl⟩
  · intro a ε hε
    exact h.small_ball_pathConnected g a hε.1 hε.2

namespace LocalGeodesic
variable [CompactSpace X] {o : X} {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)

include hr hc g in
lemma locallyPathConnected : LocallyPathConnectedSpace (LocalGeodesic o) :=
  (coverData hr hc g).locallyPathConnected g

/-- The actual unique lift between based local-geodesic covers. -/
def rebaseMap (a : LocalGeodesic o) : C(LocalGeodesic (endpoint a),LocalGeodesic o) := by
  letI := locallyPathConnected (o:=endpoint a) hr hc g
  exact ((isCoveringMap (o:=o) hr hc g).existsUnique_continuousMap_lifts
    ⟨endpoint,endpoint_continuous⟩ (constant (endpoint a)) a rfl).choose

lemma rebaseMap_start (a : LocalGeodesic o) : rebaseMap hr hc g a (constant (endpoint a))=a := by
  let := locallyPathConnected (o:=endpoint a) hr hc g
  exact ((isCoveringMap (o:=o) hr hc g).existsUnique_continuousMap_lifts
    ⟨endpoint,endpoint_continuous⟩ (constant (endpoint a)) a rfl).choose_spec.1.1
lemma rebaseMap_endpoint (a : LocalGeodesic o) (b : LocalGeodesic (endpoint a)) :
    endpoint (rebaseMap hr hc g a b)=endpoint b := by
  let := locallyPathConnected (o:=endpoint a) hr hc g
  exact congrFun (((isCoveringMap (o:=o) hr hc g).existsUnique_continuousMap_lifts
    ⟨endpoint,endpoint_continuous⟩ (constant (endpoint a)) a rfl).choose_spec.1.2) b

end LocalGeodesic
end HyperbolicObstruction
end
end

section

end

end OAI
