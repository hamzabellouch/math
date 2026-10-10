import Mathlib
import OAI.Geometry.HyperbolicGroups.DevelopmentRadial

namespace OAI

section

noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X]

def deckSubgroup (o : X) : Subgroup (LocalGeodesic o ≃ₜ LocalGeodesic o) where
  carrier := {f | ∀ a, endpoint (f a)=endpoint a}
  one_mem' := fun _ => rfl
  mul_mem' hf hg a := (hf _).trans (hg a)
  inv_mem' := by
    intro f hf a
    change endpoint (f.symm a)=endpoint a
    have hh:=hf (f.symm a)
    rw [Homeomorph.apply_symm_apply] at hh
    exact hh.symm

abbrev Deck (o : X) := deckSubgroup o

instance (o : X) : MulAction (Deck o) (LocalGeodesic o) where
  smul d a := d.val a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma deck_endpoint {o : X} (d : Deck o) (a : LocalGeodesic o) : endpoint (d • a)=endpoint a := d.property a
instance {o : X} : ContinuousConstSMul (Deck o) (LocalGeodesic o) where
  continuous_const_smul d := d.val.continuous

variable [CompactSpace X] {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}
include hr hc g
lemma deck_ext {d e : Deck o} (a : LocalGeodesic o) (h : d • a=e • a) : d=e := by
  apply Subtype.ext
  apply Homeomorph.ext
  exact congrFun ((isCoveringMap hr hc g).eq_of_comp_eq d.val.continuous e.val.continuous
    (by funext z; exact (d.property z).trans (e.property z).symm) a h)

lemma deck_exists (a b : LocalGeodesic o) (h : endpoint b=endpoint a) : ∃ d : Deck o, d • a=b := by
  exact ⟨⟨basedHomeomorph hr hc g a b h,fun z => basedLift_endpoint hr hc g a b h z⟩,
    basedLift_start hr hc g a b h⟩

omit [CompactSpace X] hr hc in
lemma endpoint_surjective : Function.Surjective (@endpoint X _ o) := by
  intro y
  exact ⟨ofReal (g.segment_spec o y).isLocalSegment (g.segment_spec o y).1,(g.segment_spec o y).2.1⟩

lemma deck_quotientCovering : IsQuotientCoveringMap (@endpoint X _ o) (Deck o) where
  toIsQuotientMap := (isCoveringMap hr hc g).isQuotientMap (endpoint_surjective g)
  continuous_const_smul d := continuous_const_smul d
  apply_eq_iff_mem_orbit := by
    intro a b
    constructor
    · intro hh
      obtain ⟨d,hd⟩:=deck_exists hr hc g b a hh
      exact ⟨d,hd⟩
    · rintro ⟨d,rfl⟩
      exact deck_endpoint d b
  disjoint a := by
    refine ⟨ball a (r/16000),ball_mem_nhds a (by positivity),?_⟩
    intro d hd
    obtain ⟨z,⟨b,hb,rfl⟩,hdb⟩:=hd
    apply deck_ext hr hc g b
    change d • b=b
    apply (coverData hr hc g).nearby_unique
    · have hh:=dist_triangle (d • b) a b
      have hb' : dist b a<r/16000 := hb
      have hd' : dist (d • b) a<r/16000 := hdb
      rw [dist_comm a b] at hh
      linarith
    · exact deck_endpoint d b

omit hr hc g in
def deckIsometry (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X) (d : Deck o) :
    letI := intrinsicMetric (o:=o) hr hc g
    LocalGeodesic o ≃ᵢ LocalGeodesic o := by
  letI := intrinsicMetric (o:=o) hr hc g
  exact {
    toEquiv := d.val.toEquiv
    isometry_toFun := Isometry.of_dist_eq (intrinsicDist_homeomorph hr hc g d.val d.property)}

omit hr hc g in
def deckIsometricAction (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X) :
    letI := intrinsicMetric (o:=o) hr hc g
    Deck o →* (LocalGeodesic o ≃ᵢ LocalGeodesic o) := by
  letI := intrinsicMetric (o:=o) hr hc g
  exact {
    toFun := deckIsometry hr hc g
    map_one' := IsometryEquiv.ext (fun _ => rfl)
    map_mul' := fun _ _ => IsometryEquiv.ext (fun _ => rfl)}

omit hr hc g in
def deckPiOneEquiv (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X) :
    FundamentalGroup X o ≃* Deck o :=
  ((deck_quotientCovering hr hc g).fundamentalGroupEquiv ⟨constant o,rfl⟩).trans (MulEquiv.inv' (Deck o)).symm

end HyperbolicObstruction.LocalGeodesic
end
end

section

end

end OAI
