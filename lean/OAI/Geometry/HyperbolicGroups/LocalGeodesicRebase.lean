import Mathlib
import OAI.Geometry.HyperbolicGroups.LocalGeodesicTopology

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o q : X}

def basedLift (a : LocalGeodesic o) (b : LocalGeodesic q) (he : endpoint b=endpoint a) :
    C(LocalGeodesic o,LocalGeodesic q) := by
  letI := locallyPathConnected (o:=o) hr hc g
  exact ((isCoveringMap (o:=q) hr hc g).existsUnique_continuousMap_lifts
    ⟨endpoint,endpoint_continuous⟩ a b he).choose

lemma basedLift_start (a : LocalGeodesic o) (b : LocalGeodesic q) (he : endpoint b=endpoint a) :
    basedLift hr hc g a b he a=b := by
  let := locallyPathConnected (o:=o) hr hc g
  exact ((isCoveringMap (o:=q) hr hc g).existsUnique_continuousMap_lifts
    ⟨endpoint,endpoint_continuous⟩ a b he).choose_spec.1.1

lemma basedLift_endpoint (a : LocalGeodesic o) (b : LocalGeodesic q) (he : endpoint b=endpoint a)
    (z : LocalGeodesic o) : endpoint (basedLift hr hc g a b he z)=endpoint z := by
  let := locallyPathConnected (o:=o) hr hc g
  exact congrFun (((isCoveringMap (o:=q) hr hc g).existsUnique_continuousMap_lifts
    ⟨endpoint,endpoint_continuous⟩ a b he).choose_spec.1.2) z

lemma basedLift_inv (a : LocalGeodesic o) (b : LocalGeodesic q) (he : endpoint b=endpoint a)
    (z : LocalGeodesic o) :
    basedLift hr hc g b a he.symm (basedLift hr hc g a b he z)=z := by
  have hh := (isCoveringMap (o:=o) hr hc g).eq_of_comp_eq
    ((basedLift hr hc g b a he.symm).continuous.comp (basedLift hr hc g a b he).continuous)
    continuous_id (by funext w; simp only [Function.comp_apply,basedLift_endpoint,id_eq]) a
    (by rw [Function.comp_apply,basedLift_start,basedLift_start]; rfl)
  exact congrFun hh z

/-- Re-basing changes the genuine local-geodesic model by a covering isomorphism. -/
def basedHomeomorph (a : LocalGeodesic o) (b : LocalGeodesic q) (he : endpoint b=endpoint a) :
    LocalGeodesic o ≃ₜ LocalGeodesic q where
  toFun := basedLift hr hc g a b he
  invFun := basedLift hr hc g b a he.symm
  left_inv := basedLift_inv hr hc g a b he
  right_inv := basedLift_inv hr hc g b a he.symm
  continuous_toFun := (basedLift hr hc g a b he).continuous
  continuous_invFun := (basedLift hr hc g b a he.symm).continuous

def rebase (a : LocalGeodesic o) : LocalGeodesic (endpoint a) ≃ₜ LocalGeodesic o :=
  basedHomeomorph hr hc g (constant (endpoint a)) a rfl

@[simp] lemma rebase_start (a : LocalGeodesic o) : rebase hr hc g a (constant (endpoint a))=a :=
  basedLift_start hr hc g _ _ _
@[simp] lemma rebase_endpoint (a : LocalGeodesic o) (b : LocalGeodesic (endpoint a)) :
    endpoint (rebase hr hc g a b)=endpoint b := basedLift_endpoint hr hc g _ _ _ _
@[simp] lemma rebase_symm_endpoint (a b : LocalGeodesic o) :
    endpoint ((rebase hr hc g a).symm b)=endpoint b := basedLift_endpoint hr hc g _ _ _ _
@[simp] lemma rebase_symm_self (a : LocalGeodesic o) : (rebase hr hc g a).symm a=constant (endpoint a) :=
  (Homeomorph.symm_apply_eq _).mpr (rebase_start hr hc g a).symm

end HyperbolicObstruction.LocalGeodesic
end
end

section

end

end OAI
