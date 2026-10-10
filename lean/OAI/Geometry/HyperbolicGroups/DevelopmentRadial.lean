import Mathlib
import OAI.Geometry.HyperbolicGroups.DevelopmentGeodesic

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o q : X}

lemma intrinsicDist_map_le (F : C(LocalGeodesic o,LocalGeodesic q))
    (hp : ∀ a, endpoint (F a)=endpoint a) (a b : LocalGeodesic o) :
    intrinsicDist hr hc g (F a) (F b)≤ intrinsicDist hr hc g a b := by
  let c := (rebase hr hc g a).symm b
  let rho2 : C(I,LocalGeodesic (endpoint (F a))) :=
    (⟨(rebase hr hc g (F a)).symm,(rebase hr hc g (F a)).symm.continuous⟩ : C(_,_)).comp
      (F.comp (joining hr hc g a b))
  have hh := length_variation hr hc g c.localSegment rho2
    (fun t => by change endpoint ((rebase hr hc g (F a)).symm (F (joining hr hc g a b t)))=extend c.val t
                 rw [rebase_symm_endpoint,hp,joining_endpoint,extend_coe]) 0 1
  simpa [rho2,c,intrinsicDist,abs_of_nonneg (length_nonneg _)] using hh

lemma intrinsicDist_homeomorph (F : LocalGeodesic o ≃ₜ LocalGeodesic q)
    (hp : ∀ a, endpoint (F a)=endpoint a) (a b : LocalGeodesic o) :
    intrinsicDist hr hc g (F a) (F b)=intrinsicDist hr hc g a b := by
  apply le_antisymm (intrinsicDist_map_le hr hc g ⟨F,F.continuous⟩ hp a b)
  have hpinv : ∀ z, endpoint (F.symm z)=endpoint z := fun z => by simpa using (hp (F.symm z)).symm
  simpa using intrinsicDist_map_le hr hc g ⟨F.symm,F.symm.continuous⟩ hpinv (F a) (F b)

lemma intrinsicDist_rebase (a : LocalGeodesic o) (b c : LocalGeodesic (endpoint a)) :
    intrinsicDist hr hc g (rebase hr hc g a b) (rebase hr hc g a c)=intrinsicDist hr hc g b c :=
  intrinsicDist_homeomorph hr hc g (rebase hr hc g a) (rebase_endpoint hr hc g a) b c

include hr hc g in
omit [CompactSpace X] in
lemma initial_close_dist_le (t : I) {a b : LocalGeodesic o} (hab : dist a b<r/10) :
    dist (initial t a) (initial t b)≤(t:ℝ)*dist a b := by
  apply (ContinuousMap.dist_le (mul_nonneg t.property.1 dist_nonneg)).mpr
  intro u
  change dist (initial t a u) (initial t b u)≤_
  rw [prefix_apply,prefix_apply]
  have hh := a.localSegment.close_chord b.localSegment hr hc g
    (fun s hs => by rw [extend_mem _ hs,extend_mem _ hs]; exact (ContinuousMap.dist_apply_le_dist (⟨s,hs⟩:I)).trans_lt hab)
    ((u:ℝ)*t) (u*t).property
  simp only [show (u:ℝ)*(t:ℝ)=((u*t:I):ℝ) from rfl,extend_coe,extend_zero,extend_one,a.start,b.start,dist_self,mul_zero,zero_add] at hh
  apply hh.trans
  have he : dist (a 1) (b 1)≤dist a b := ContinuousMap.dist_apply_le_dist (1:I)
  change (u:ℝ)*(t:ℝ)*dist (a 1) (b 1)≤(t:ℝ)*dist a b
  nlinarith [u.property.2,t.property.1,dist_nonneg (x:=a 1) (y:=b 1),mul_nonneg t.property.1 (sub_nonneg.mpr u.property.2)]

lemma initial_intrinsicDist_le (t : I) (a b : LocalGeodesic o) :
    intrinsicDist hr hc g (initial t a) (initial t b)≤(t:ℝ)*intrinsicDist hr hc g a b := by
  let ρ:=joining hr hc g a b
  obtain ⟨ε,hε,he⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous ρ.continuous) (r/8000) (by positivity)
  have hh := @local_dist_le_global (LocalGeodesic o) (intrinsicMetric hr hc g)
    (fun u => initial t (ρ (projIcc 0 1 zero_le_one u))) ((t:ℝ)*intrinsicDist hr hc g a b) ε hε
    (by intro u hu v hv huv
        simp only [projIcc_of_mem zero_le_one hu,projIcc_of_mem zero_le_one hv]
        have huv' : dist (ρ ⟨u,hu⟩) (ρ ⟨v,hv⟩)<r/8000 := he (by simpa [Subtype.dist_eq,Real.dist_eq] using huv)
        have hi := initial_close_dist_le hr hc g t (by linarith : dist (ρ ⟨u,hu⟩) (ρ ⟨v,hv⟩)<r/10)
        have hti : (t:ℝ)*dist (ρ ⟨u,hu⟩) (ρ ⟨v,hv⟩)≤dist (ρ ⟨u,hu⟩) (ρ ⟨v,hv⟩) := by
          nlinarith [t.property.2,dist_nonneg (x:=ρ ⟨u,hu⟩) (y:=ρ ⟨v,hv⟩)]
        change intrinsicDist hr hc g (initial t (ρ ⟨u,hu⟩)) (initial t (ρ ⟨v,hv⟩))≤_
        rw [intrinsicDist_eq_of_close hr hc g ((hi.trans hti).trans_lt huv')]
        apply hi.trans
        have hd := ordinary_dist_le_intrinsic hr hc g (ρ ⟨u,hu⟩) (ρ ⟨v,hv⟩)
        rw [show intrinsicDist hr hc g (ρ ⟨u,hu⟩) (ρ ⟨v,hv⟩)=|u-v| *intrinsicDist hr hc g a b from intrinsicDist_joining hr hc g a b ⟨u,hu⟩ ⟨v,hv⟩] at hd
        simpa only [mul_left_comm (t:ℝ)] using mul_le_mul_of_nonneg_left hd t.property.1)
    (s:=0) (t:=1) (by norm_num) (by norm_num)
  change intrinsicDist hr hc g (initial t (ρ _)) (initial t (ρ _))≤_ at hh
  simpa [ρ] using hh

lemma joining_radial (a b c : LocalGeodesic o) (t : I) :
    intrinsicDist hr hc g (joining hr hc g a b t) (joining hr hc g a c t)≤(t:ℝ)*intrinsicDist hr hc g b c := by
  dsimp only [joining,ContinuousMap.coe_mk]
  rw [intrinsicDist_rebase]
  have hh := initial_intrinsicDist_le hr hc g t ((rebase hr hc g a).symm b) ((rebase hr hc g a).symm c)
  have he := intrinsicDist_rebase hr hc g a ((rebase hr hc g a).symm b) ((rebase hr hc g a).symm c)
  simpa only [Homeomorph.apply_symm_apply] using hh.trans_eq (congrArg ((t:ℝ)*·) he.symm)

lemma developed_radial : @RadialBusemann (LocalGeodesic o) (intrinsicMetric hr hc g) := by
  intro a b c α β hα hβ t ht
  rw [developedSegment_unique hr hc g hα ht,developedSegment_unique hr hc g hβ ht]
  change intrinsicDist hr hc g (developedSegment hr hc g a b t) (developedSegment hr hc g a c t)≤t*intrinsicDist hr hc g b c
  simp only [developedSegment,projIcc_of_mem zero_le_one ht]
  exact joining_radial hr hc g a b c ⟨t,ht⟩

end HyperbolicObstruction.LocalGeodesic
end
end

section

end

end OAI
