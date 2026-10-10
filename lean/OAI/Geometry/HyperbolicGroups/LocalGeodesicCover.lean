import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedFillingValue
import OAI.Geometry.HyperbolicGroups.LocalSegmentTools
import OAI.Geometry.HyperbolicGroups.LocalSegmentContinuation
import OAI.Geometry.HyperbolicGroups.UniformMetricCover

namespace OAI

section


/-! The space of genuine local geodesics based at a point, with its uniform
function-space topology. The endpoint map is a produced covering map. -/
noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

lemma IsLocalSegment.congr {α β : ℝ → X} {A : ℝ} (h : IsLocalSegment α A)
    (he : EqOn α β (Icc 0 1)) : IsLocalSegment β A := by
  refine ⟨h.nonneg,h.continuousOn.congr (fun t ht => (he ht).symm),?_⟩
  obtain ⟨ε,hε,hd⟩ := h.local_dist
  exact ⟨ε,hε,fun s hs t ht hst => by rw [←he hs,←he ht]; exact hd s hs t ht hst⟩

namespace LocalGeodesic

def extend (γ : C(I,X)) (t : ℝ) : X := γ (projIcc 0 1 zero_le_one t)
@[simp] lemma extend_coe (γ : C(I,X)) (t : I) : extend γ t=γ t := by simp [extend]
lemma extend_mem (γ : C(I,X)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : extend γ t=γ ⟨t,ht⟩ := by
  simp only [extend,projIcc_of_mem zero_le_one ht]
@[simp] lemma extend_zero (γ : C(I,X)) : extend γ 0=γ 0 := by simpa using extend_coe γ 0
@[simp] lemma extend_one (γ : C(I,X)) : extend γ 1=γ 1 := by simpa using extend_coe γ 1

end LocalGeodesic

def LocalGeodesic (o : X) := {γ : C(I,X) // γ 0=o ∧ ∃ L : ℝ, IsLocalSegment (LocalGeodesic.extend γ) L}

namespace LocalGeodesic
variable {o : X}
instance : MetricSpace (LocalGeodesic o) := inferInstanceAs (MetricSpace (Subtype _))
instance : CoeFun (LocalGeodesic o) (fun _ => I → X) := ⟨fun γ => γ.val⟩

lemma start (γ : LocalGeodesic o) : γ 0=o := γ.property.1

def length (γ : LocalGeodesic o) : ℝ := γ.property.2.choose
lemma localSegment (γ : LocalGeodesic o) : IsLocalSegment (extend γ.val) γ.length := γ.property.2.choose_spec
lemma length_nonneg (γ : LocalGeodesic o) : 0≤γ.length := γ.localSegment.nonneg

def endpoint (γ : LocalGeodesic o) : X := γ 1
lemma endpoint_lipschitz : LipschitzWith 1 (@endpoint X _ o) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change dist (a.val (1:I)) (b.val (1:I)) ≤ (1:ℝ)*dist a.val b.val
  simpa only [one_mul] using ContinuousMap.dist_apply_le_dist (f:=a.val) (g:=b.val) (1:I)
lemma endpoint_continuous : Continuous (@endpoint X _ o) := endpoint_lipschitz.continuous

@[ext] lemma ext {a b : LocalGeodesic o} (he : ∀ t, a t=b t) : a=b :=
  Subtype.ext (ContinuousMap.ext he)

def ofReal {α : ℝ → X} {A : ℝ} (h : IsLocalSegment α A) (h0 : α 0=o) : LocalGeodesic o :=
  ⟨⟨fun t => α t,continuousOn_iff_continuous_domRestrict.mp h.continuousOn⟩,h0,A,h.congr (fun t ht => by change α t = α ((projIcc 0 1 zero_le_one t : I) : ℝ); rw [projIcc_of_mem zero_le_one ht])⟩
@[simp] lemma ofReal_apply {α : ℝ → X} {A : ℝ} (h : IsLocalSegment α A) (h0 : α 0=o) (t : I) : ofReal h h0 t=α t := rfl
lemma ofReal_length {α : ℝ → X} {A : ℝ} (h : IsLocalSegment α A) (h0 : α 0=o) :
    (ofReal h h0).length=A := by
  apply (ofReal h h0).localSegment.length_unique
  exact h.congr (fun t ht => by change α t = α ((projIcc 0 1 zero_le_one t : I) : ℝ); rw [projIcc_of_mem zero_le_one ht])

def constant (o : X) : LocalGeodesic o := ofReal (α:=fun _ => o)
  ⟨le_rfl,continuousOn_const,1,by norm_num,by intro s hs t ht hst; simp⟩ rfl
@[simp] lemma constant_apply (o : X) (t : I) : constant o t=o := rfl
instance : Nonempty (LocalGeodesic o) := ⟨constant o⟩

lemma close_isometry {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
    {a b : LocalGeodesic o} (hab : dist a b<r/10) : dist (endpoint a) (endpoint b)=dist a b := by
  apply le_antisymm (by simpa only [NNReal.coe_one,one_mul] using endpoint_lipschitz.dist_le_mul a b)
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  have hh := a.localSegment.close_chord b.localSegment hr hc g
    (fun u hu => by rw [extend_mem _ hu,extend_mem _ hu]; exact (ContinuousMap.dist_apply_le_dist (⟨u,hu⟩:I)).trans_lt hab) t t.property
  simp only [extend_coe,extend_zero,extend_one,a.start,b.start,dist_self,mul_zero,zero_add] at hh
  exact hh.trans (by change (t:ℝ)*dist (a 1) (b 1)≤dist (a 1) (b 1); nlinarith [t.property.2,dist_nonneg (x:=a 1) (y:=b 1)])

variable [CompactSpace X]
lemma short_lift {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
    (a : LocalGeodesic o) (y : X) (hy : dist y (endpoint a)<r/2000) :
    ∃ b : LocalGeodesic o, endpoint b=y ∧ dist b a=dist y (endpoint a) := by
  obtain ⟨β,B,hβ,hβ0,hβ1,hclose⟩ := a.localSegment.continuation hr hc g
    (a:=o) (b:=y) (by rw [extend_zero,a.start,dist_self]; positivity) (by simpa [endpoint] using hy.le)
  let b : LocalGeodesic o := ofReal hβ hβ0
  have hb1 : endpoint b=y := hβ1
  have hba : dist b a≤dist y (endpoint a) := by
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro t
    have hh := hclose t t.property
    simp only [extend_coe,extend_zero,extend_one,a.start,dist_self,mul_zero,zero_add] at hh
    change dist (β t) (a t)≤_
    rw [dist_comm]
    apply hh.trans
    rw [dist_comm (a 1) y]
    change (t:ℝ)*dist y (a 1)≤dist y (a 1)
    nlinarith [t.property.2,dist_nonneg (x:=y) (y:=a 1)]
  refine ⟨b,hb1,le_antisymm hba ?_⟩
  rw [←hb1]
  exact by simpa using endpoint_lipschitz.dist_le_mul b a

lemma coverData {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X) :
    UniformMetricCoverData (@endpoint X _ o) (r/2000) := by
  refine ⟨by positivity,fun a b hab => close_isometry hr hc g (by linarith),short_lift hr hc g⟩

lemma isCoveringMap {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X) :
    IsCoveringMap (@endpoint X _ o) := (coverData hr hc g).isCoveringMap

end LocalGeodesic
end HyperbolicObstruction
end
end

section

end

end OAI
