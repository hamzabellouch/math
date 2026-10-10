import Mathlib
import OAI.Geometry.HyperbolicGroups.DevelopmentDeck
import OAI.Geometry.HyperbolicGroups.DevelopmentProper

namespace OAI

section

noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}

lemma rebase_constant_apply (a : LocalGeodesic o) : rebase hr hc g (constant o) a=a := by
  apply congrFun ((isCoveringMap hr hc g).eq_of_comp_eq (rebase hr hc g (constant o)).continuous continuous_id
    (by funext z; exact rebase_endpoint hr hc g (constant o) z) (constant o) (rebase_start hr hc g (constant o)))

lemma intrinsicDist_constant (a : LocalGeodesic o) : intrinsicDist hr hc g (constant o) a=a.length := by
  have hh : (rebase hr hc g (constant o)).symm a=a := by
    apply (Homeomorph.symm_apply_eq _).mpr
    exact (rebase_constant_apply hr hc g a).symm
  unfold intrinsicDist
  exact congrArg (@length X _ o) hh

def deckGeometricAction : @GeometricAction (Deck o) (LocalGeodesic o) _ (intrinsicMetric hr hc g) := by
  have hdisc := (coverData (o:=o) hr hc g).discrete_fiber o
  letI := intrinsicMetric (o:=o) hr hc g
  letI := developed_proper (o:=o) hr hc g
  refine ⟨deckIsometricAction hr hc g,?_,?_⟩
  · intro C hC
    let a : LocalGeodesic o := constant o
    obtain ⟨R,hR⟩:=hC.isBounded.subset_closedBall a
    let F : Set (LocalGeodesic o) := endpoint ⁻¹' {o}
    have hFclosed : IsClosed F := isClosed_singleton.preimage endpoint_continuous
    have hFdisc : IsDiscrete F := isDiscrete_iff_discreteTopology.mpr hdisc
    have hfin : (closedBall a (2*R) ∩ F).Finite :=
      ((isCompact_closedBall a (2*R)).inter_right hFclosed).finite (hFdisc.mono inter_subset_right)
    have hmap : Function.Injective (fun d : Deck o => d • a) := fun d e h => deck_ext hr hc g a h
    apply ((hfin.preimage hmap.injOn)).subset
    intro d hd
    obtain ⟨x,hx,hdx⟩:=hd
    refine ⟨?_,?_⟩
    · have hx' : dist x a≤R := hR hx
      have hdx' : dist (d • x) a≤R := hR hdx
      have he : dist (d • a) (d • x)=dist a x := (deckIsometry hr hc g d).isometry.dist_eq a x
      have ht:=dist_triangle (d • a) (d • x) a
      rw [he,dist_comm a x] at ht
      exact ht.trans (by linarith)
    · change endpoint (d • a)=o
      rw [deck_endpoint]
      rfl
  · obtain ⟨R,hR⟩:=(isCompact_univ : IsCompact (univ : Set X)).isBounded.subset_closedBall o
    refine ⟨closedBall (constant o) R,isCompact_closedBall _ _,?_⟩
    intro b
    let c : LocalGeodesic o := ofReal (g.segment_spec o (endpoint b)).isLocalSegment (g.segment_spec o (endpoint b)).1
    have hcend : endpoint c=endpoint b := (g.segment_spec o (endpoint b)).2.1
    have hcC : c ∈ closedBall (constant o) R := by
      change intrinsicDist hr hc g c (constant o)≤R
      rw [intrinsicDist_comm,intrinsicDist_constant]
      change (ofReal (g.segment_spec o (endpoint b)).isLocalSegment (g.segment_spec o (endpoint b)).1).length≤R
      rw [ofReal_length]
      have hh : dist (endpoint b) o≤R := hR (mem_univ _)
      simpa [dist_comm] using hh
    obtain ⟨d,hd⟩:=deck_exists hr hc g c b hcend.symm
    exact ⟨d,c,hcC,hd⟩

end HyperbolicObstruction.LocalGeodesic
end
end

section

end

end OAI
