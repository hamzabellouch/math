import Mathlib
import OAI.Geometry.HyperbolicGroups.LocalGeodesicDistance

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {E X : Type*} [MetricSpace E] [MetricSpace X]

lemma UniformMetricCoverData.shortSegmentLift {p : E → X} {r : ℝ}
    (h : UniformMetricCoverData p r) (g : IsGeodesic X)
    {a b : E} (hab : dist a b<r/4) :
    ∃ ρ : C(I,E), ρ 0=a ∧ ρ 1=b ∧ ∀ t : I, p (ρ t)=g.segment (p a) (p b) t := by
  have hpab : dist (p a) (p b)=dist a b := h.local_dist a b (by linarith [h.positive])
  let γ:=g.segment (p a) (p b)
  have hγ:=g.segment_spec (p a) (p b)
  have hm (t : I) : γ t ∈ ball (p a) (r/4) := by
    rw [mem_ball,dist_comm,hγ.dist_from_source t.property,hpab]
    have hh : (t:ℝ)*dist a b≤dist a b := by nlinarith [t.property.2,dist_nonneg (x:=a) (y:=b)]
    exact hh.trans_lt hab
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
  exact ⟨⟨f,hf⟩,h0,h1,fun t => h.out_proj _ _ _⟩

namespace LocalGeodesic
variable [CompactSpace X] {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}

lemma intrinsicDist_eq_of_close {a b : LocalGeodesic o} (hab : dist a b<r/8000) :
    intrinsicDist hr hc g a b=dist a b := by
  apply le_antisymm _ (ordinary_dist_le_intrinsic hr hc g a b)
  obtain ⟨ρ,h0,h1,hp⟩ := (coverData hr hc g).shortSegmentLift g (by linarith : dist a b<(r/2000)/4)
  let rho2 : C(I,LocalGeodesic (endpoint a)) := (⟨(rebase hr hc g a).symm,(rebase hr hc g a).symm.continuous⟩ : C(_, _)).comp ρ
  have hh := length_variation hr hc g (g.segment_spec (endpoint a) (endpoint b)).isLocalSegment rho2
    (fun t => by change endpoint ((rebase hr hc g a).symm (ρ t))=_; rw [rebase_symm_endpoint]; exact hp t) 0 1
  have hh' : intrinsicDist hr hc g a b≤dist (endpoint a) (endpoint b) := by
    simpa [rho2,h0,h1,intrinsicDist,abs_of_nonneg (length_nonneg _)] using hh
  exact hh'.trans (by simpa using endpoint_lipschitz.dist_le_mul a b)

@[instance_reducible] def intrinsicMetric : MetricSpace (LocalGeodesic o) :=
  MetricSpace.ofDistTopology (intrinsicDist hr hc g) (intrinsicDist_self hr hc g)
    (intrinsicDist_comm hr hc g) (intrinsicDist_triangle hr hc g)
    (by intro s
        rw [Metric.isOpen_iff]
        constructor
        · intro hs a ha
          obtain ⟨ε,hε,he⟩:=hs a ha
          exact ⟨ε,hε,fun b hb => he (by rw [mem_ball,dist_comm]; exact (ordinary_dist_le_intrinsic hr hc g a b).trans_lt hb)⟩
        · intro hs a ha
          obtain ⟨ε,hε,he⟩:=hs a ha
          refine ⟨min ε (r/8000),lt_min hε (by positivity),fun b hb => ?_⟩
          have hb' : dist a b< min ε (r/8000) := by simpa [mem_ball,dist_comm] using hb
          apply he b
          rw [intrinsicDist_eq_of_close hr hc g (lt_min_iff.mp hb').2]
          exact (lt_min_iff.mp hb').1)
    (fun _ _ => intrinsicDist_eq_zero hr hc g)

end LocalGeodesic
end HyperbolicObstruction
end
end

section

end

end OAI
