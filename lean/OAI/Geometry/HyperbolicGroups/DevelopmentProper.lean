import Mathlib
import OAI.Geometry.HyperbolicGroups.DevelopmentGeodesic
import OAI.Geometry.HyperbolicGroups.UniformGeodesicProper

namespace OAI

section

noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {E X : Type*} [MetricSpace E] [MetricSpace X]

lemma UniformMetricCoverData.isCompact_closedBall [ProperSpace X] {p : E → X} {r : ℝ}
    (h : UniformMetricCoverData p r) (a : E) {ε : ℝ} (hε : ε<r/4) :
    IsCompact (closedBall a ε) := by
  let f : closedBall (p a) ε → E := fun y => (h.out (p a) ⟨a,rfl⟩ ⟨y.val,y.property.trans_lt hε⟩).val
  have hf : Continuous f := continuous_subtype_val.comp ((h.out_isometry (p a) ⟨a,rfl⟩).continuous.comp
    (continuous_subtype_val.subtype_mk (fun y => y.property.trans_lt hε)))
  have he : range f=closedBall a ε := by
    ext b
    constructor
    · rintro ⟨y,rfl⟩
      change dist (f y) a≤ε
      rw [show dist (f y) a=dist y.val (p a) from h.out_dist _ _ _]
      exact y.property
    · intro hb
      have hba : dist b a≤ε := hb
      have hpba : dist (p b) (p a)=dist b a := h.local_dist _ _ (by linarith [h.positive])
      let y : closedBall (p a) ε := ⟨p b,by change dist (p b) (p a)≤ε; rw [hpba]; exact hba⟩
      refine ⟨y,?_⟩
      apply h.nearby_unique
      · have hh := dist_triangle (f y) a b
        rw [show dist (f y) a=dist y.val (p a) from h.out_dist _ _ _,dist_comm a b] at hh
        change dist (p b) (p a)+dist b a≥dist (f y) b at hh
        rw [hpba] at hh
        linarith [h.positive]
      · exact h.out_proj _ _ _
  rw [←he]
  exact isCompact_range hf

namespace LocalGeodesic
variable [CompactSpace X] {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}

lemma developed_smallBall_compact (a : LocalGeodesic o) :
    @IsCompact (LocalGeodesic o) (intrinsicMetric hr hc g).toUniformSpace.toTopologicalSpace
      (@closedBall (LocalGeodesic o) (intrinsicMetric hr hc g).toPseudoMetricSpace a (r/32000)) := by
  have he : @closedBall (LocalGeodesic o) (intrinsicMetric hr hc g).toPseudoMetricSpace a (r/32000)=
      closedBall a (r/32000) := by
    ext b
    change intrinsicDist hr hc g b a≤r/32000 ↔ dist b a≤r/32000
    constructor
    · intro h; exact (ordinary_dist_le_intrinsic hr hc g b a).trans h
    · intro h
      rw [intrinsicDist_eq_of_close hr hc g (by linarith : dist b a<r/8000)]
      exact h
  rw [he]
  exact (coverData hr hc g).isCompact_closedBall a (by linarith : r/32000<(r/2000)/4)

lemma developed_proper : @ProperSpace (LocalGeodesic o) (intrinsicMetric hr hc g).toPseudoMetricSpace :=
  @proper_of_uniform_compact_balls (LocalGeodesic o) (intrinsicMetric hr hc g)
    (developed_isGeodesic hr hc g) (r/32000) (by positivity) (developed_smallBall_compact hr hc g)
end LocalGeodesic
end HyperbolicObstruction
end
end

section

end

end OAI
