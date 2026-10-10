import Mathlib
import OAI.Geometry.HyperbolicGroups.ShortSegmentLift

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}

lemma joining_length_variation (x a b : LocalGeodesic o) (s t : I) :
    |intrinsicDist hr hc g x (joining hr hc g a b s)-intrinsicDist hr hc g x (joining hr hc g a b t)|≤
      |(s:ℝ)-t| *intrinsicDist hr hc g a b := by
  let c := (rebase hr hc g a).symm b
  let rho2 : C(I,LocalGeodesic (endpoint x)) :=
    (⟨(rebase hr hc g x).symm,(rebase hr hc g x).symm.continuous⟩ : C(_,_)).comp (joining hr hc g a b)
  have hh := length_variation hr hc g c.localSegment rho2 (fun t => by simp [rho2,c]) s t
  exact hh

lemma intrinsicDist_joining_le (a b : LocalGeodesic o) (s t : I) :
    intrinsicDist hr hc g (joining hr hc g a b s) (joining hr hc g a b t)≤
      |(s:ℝ)-t| *intrinsicDist hr hc g a b := by
  have hh := joining_length_variation hr hc g (joining hr hc g a b s) a b s t
  simpa only [intrinsicDist_self,zero_sub,abs_neg,abs_of_nonneg (intrinsicDist_nonneg hr hc g _ _)] using hh

lemma intrinsicDist_to_joining (a b : LocalGeodesic o) (t : I) :
    intrinsicDist hr hc g a (joining hr hc g a b t)=(t:ℝ)*intrinsicDist hr hc g a b := by
  simp [intrinsicDist,joining]

lemma intrinsicDist_joining (a b : LocalGeodesic o) (s t : I) :
    intrinsicDist hr hc g (joining hr hc g a b s) (joining hr hc g a b t)=
      |(s:ℝ)-t| *intrinsicDist hr hc g a b := by
  apply le_antisymm (intrinsicDist_joining_le hr hc g a b s t)
  have hh := intrinsicDist_variation hr hc g a (joining hr hc g a b s) (joining hr hc g a b t)
  rw [intrinsicDist_to_joining,intrinsicDist_to_joining,←sub_mul,abs_mul,abs_of_nonneg (intrinsicDist_nonneg hr hc g a b)] at hh
  exact hh

def developedSegment (a b : LocalGeodesic o) (t : ℝ) : LocalGeodesic o :=
  joining hr hc g a b (projIcc 0 1 zero_le_one t)

lemma developedSegment_spec (a b : LocalGeodesic o) :
    @IsSegment (LocalGeodesic o) (intrinsicMetric hr hc g) (developedSegment hr hc g a b) a b := by
  refine ⟨by simp [developedSegment],by simp [developedSegment],?_⟩
  intro s hs t ht
  change intrinsicDist hr hc g (developedSegment hr hc g a b s) (developedSegment hr hc g a b t)=|s-t| *intrinsicDist hr hc g a b
  simp only [developedSegment,projIcc_of_mem zero_le_one hs,projIcc_of_mem zero_le_one ht]
  exact intrinsicDist_joining hr hc g a b ⟨s,hs⟩ ⟨t,ht⟩

lemma developed_isGeodesic : @IsGeodesic (LocalGeodesic o) (intrinsicMetric hr hc g) :=
  fun a b => ⟨developedSegment hr hc g a b,developedSegment_spec hr hc g a b⟩

lemma endpoint_dist_le_intrinsic (a b : LocalGeodesic o) :
    dist (endpoint a) (endpoint b)≤ intrinsicDist hr hc g a b := by
  have h : dist (endpoint a) (endpoint b)≤dist a b := by simpa using endpoint_lipschitz.dist_le_mul a b
  exact h.trans (ordinary_dist_le_intrinsic hr hc g a b)

lemma endpoint_dist_eq_of_short {a b : LocalGeodesic o} (h : intrinsicDist hr hc g a b<r/8000) :
    dist (endpoint a) (endpoint b)=intrinsicDist hr hc g a b := by
  have hab : dist a b<r/8000 := (ordinary_dist_le_intrinsic hr hc g a b).trans_lt h
  rw [intrinsicDist_eq_of_close hr hc g hab,close_isometry hr hc g (by linarith)]

lemma projected_localSegment {α : ℝ → LocalGeodesic o} {a b : LocalGeodesic o}
    (hα : @IsSegment (LocalGeodesic o) (intrinsicMetric hr hc g) α a b) :
    IsLocalSegment (fun t => endpoint (α t)) (intrinsicDist hr hc g a b) := by
  let A := intrinsicDist hr hc g a b
  have hA : 0≤A := intrinsicDist_nonneg hr hc g a b
  have hcont : ContinuousOn α (Icc 0 1) := @IsSegment.continuousOn _ (intrinsicMetric hr hc g) _ _ _ hα
  refine ⟨hA,endpoint_continuous.comp_continuousOn hcont,r/(8000*(1+A)),by positivity,?_⟩
  intro s hs t ht hst
  have hh : |s-t| *A<r/8000 := by
    have hv := (lt_div_iff₀ (by positivity : 0<8000*(1+A))).mp hst
    have hab:=abs_nonneg (s-t)
    nlinarith
  have he : intrinsicDist hr hc g (α s) (α t)=|s-t| *A := hα.2.2 s hs t ht
  rw [endpoint_dist_eq_of_short hr hc g (by rw [he]; exact hh),he]

lemma developedSegment_unique {α : ℝ → LocalGeodesic o} {a b : LocalGeodesic o}
    (hα : @IsSegment (LocalGeodesic o) (intrinsicMetric hr hc g) α a b) :
    EqOn α (developedSegment hr hc g a b) (Icc 0 1) := by
  let c : LocalGeodesic (endpoint a) := ofReal (projected_localSegment hr hc g hα) (by rw [hα.1])
  let p : C(I,LocalGeodesic o) := ⟨fun t => α t,continuousOn_iff_continuous_domRestrict.mp
    (@IsSegment.continuousOn _ (intrinsicMetric hr hc g) _ _ _ hα)⟩
  let q : C(I,LocalGeodesic o) := ⟨fun t => rebase hr hc g a (initial t c),
    (rebase hr hc g a).continuous.comp (prefix_continuous.comp (continuous_id.prodMk continuous_const))⟩
  have he : (p : I → LocalGeodesic o)=q := (isCoveringMap hr hc g).eq_of_comp_eq p.continuous q.continuous
    (by
      funext t
      change endpoint (α t)=endpoint (rebase hr hc g a (initial t c))
      rw [rebase_endpoint,endpoint_prefix]
      rfl) 0 (by
      change α 0=rebase hr hc g a (initial 0 c)
      rw [prefix_zero,rebase_start,hα.1])
  have hend : rebase hr hc g a c=b := by
    have ht := congrFun he 1
    change α 1=rebase hr hc g a (initial 1 c) at ht
    simpa [hα.2.1] using ht.symm
  have hc' : c=(rebase hr hc g a).symm b := (Homeomorph.eq_symm_apply _).mpr hend
  intro t ht
  have hh:=congrFun he ⟨t,ht⟩
  change α t=rebase hr hc g a (initial ⟨t,ht⟩ c) at hh
  simpa [developedSegment,joining,hc',projIcc_of_mem zero_le_one ht] using hh

end HyperbolicObstruction.LocalGeodesic
end
end

section

end

end OAI
