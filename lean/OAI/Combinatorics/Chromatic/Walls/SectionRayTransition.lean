import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteRayGeometry
import OAI.Combinatorics.Chromatic.Walls.FiniteElementaryAdjoint
import OAI.Combinatorics.Chromatic.QuantumTorus.SectionCharts

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma section_ray_positive_side (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ) (p : M) (h k H : M →+ ℝ)
    (hg : RayGeneric C N p h) (hkp : 0<k p)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k H m) :
    ∀n≤N,coeff n (sectionValue v Ω C F H X)=coeff n (sectionValue v Ω C F h X) := by
  have HD:=RayGeneric.ray_supported v Ω C hg F
  have Hneg:=chartNegative_of_positive_through v Ω C k (chartZero v Ω C h F) N (by
    intro n hn m hm
    exact ((by_contra fun hr=>hm (HD (n+1) (by omega) hn m hr) : OnPositiveRay p m).eval k).1.mpr hkp)
  intro n hn
  rw [section_refinement_through v Ω C h k H F X N hs n hn]
  have HE:=adjoint_coeff_congr (chartNegative v Ω C k (chartZero v Ω C h F)).val 1
    (sectionValue v Ω C F h X) (sectionValue v Ω C F h X) n
    (fun j hj=>Hneg j (hj.trans hn)) (fun _ _=>rfl)
  rw [HE,adjoint_one]
lemma section_ray_negative_side (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ) (p : M) (h k H : M →+ ℝ)
    (hg : RayGeneric C N p h) (hkp : k p<0)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k H m) :
    ∀n≤N,coeff n (sectionValue v Ω C F H X)=
      coeff n (adjoint (chartZero v Ω C h F).val (sectionValue v Ω C F h X)) := by
  have HD:=RayGeneric.ray_supported v Ω C hg F
  have Hneg:=chartNegative_of_negative_through v Ω C k (chartZero v Ω C h F) N (by
    intro n hn m hm
    exact ((by_contra fun hr=>hm (HD (n+1) (by omega) hn m hr) : OnPositiveRay p m).eval k).2.2.mpr hkp)
  intro n hn
  rw [section_refinement_through v Ω C h k H F X N hs n hn]
  exact adjoint_coeff_congr _ _ _ _ n (fun j hj=>Hneg j (hj.trans hn)) (fun _ _=>rfl)
lemma section_ray_crossing (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ) (p : M) (h k Hplus Hminus : M →+ ℝ)
    (hg : RayGeneric C N p h)
    (hsplus : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k Hplus m)
    (hsminus : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h (-k) Hminus m) :
    (0<k p → ∀n≤N,coeff n (sectionValue v Ω C F Hminus X)=
      coeff n (adjoint (chartZero v Ω C h F).val (sectionValue v Ω C F Hplus X))) ∧
    (k p<0 → ∀n≤N,coeff n (sectionValue v Ω C F Hminus X)=
      coeff n (adjoint (invOfUnit (chartZero v Ω C h F).val 1) (sectionValue v Ω C F Hplus X))) := by
  constructor
  · intro hp n hn
    rw [section_ray_negative_side v Ω C F X N p h (-k) Hminus hg (by simpa using neg_neg_of_pos hp) hsminus n hn]
    exact adjoint_coeff_congr _ _ _ _ n (fun _ _=>rfl)
      (fun j hj=>(section_ray_positive_side v Ω C F X N p h k Hplus hg hp hsplus j (hj.trans hn)).symm)
  · intro hp n hn
    rw [section_ray_positive_side v Ω C F X N p h (-k) Hminus hg (by simpa using neg_pos.mpr hp) hsminus n hn]
    exact (adjoint_inverse_coeff _ _ _ (chartZero v Ω C h F).property.1 n
      (fun j hj=>section_ray_negative_side v Ω C F X N p h k Hplus hg hp hsplus j (hj.trans hn))).symm
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry PowerSeriesSplit PowerSeriesAdjoint
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
def ChamberGeneric (N : ℕ) (h : M →+ ℝ) : Prop :=
  ∀n,0<n → n≤N → ∀m,HasRootDegree C n m → h m≠0
include hdeg in
lemma realRoot_ne_zero (d : ℕ) (hd : 0<d) (p : M) (hp : HasRootDegree C d p) : e p≠0 := by
  intro hh
  have H:=hdeg d p hp
  rw [hh,map_zero] at H
  have hdR : (0:ℝ)<d:=by exact_mod_cast hd
  linarith
omit [Module ℝ E] in
lemma realRoot_exists (N : ℕ) (s : E) (hs : s∈realRootsThrough e C N) :
    ∃p d,d≤N ∧ HasRootDegree C d p ∧ e p=s := by
  classical
  obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hs
  obtain ⟨d,hd,hp⟩:=Finset.mem_biUnion.mp hp
  refine ⟨p,d,by have H:=Finset.mem_range.mp hd; omega,?_,rfl⟩
  simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hp
include he hdeg in
lemma section_event_ray (N : ℕ) (v k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : a∈lineEvents (realRootsThrough e C N) v k) :
    ∃p d,0<d ∧ d≤N ∧ HasRootDegree C d p ∧ v (e p)≠0 ∧
      RayGeneric C N p ((k+a • v).toAddMonoidHom.comp e) := by
  obtain ⟨s,hs,hv,hsa⟩:=(mem_lineEvents_iff _ _ _ _).mp ha
  obtain ⟨p,d,hd,hp,rfl⟩:=realRoot_exists C e N s hs
  have hd0 : 0<d:=by
    by_contra hh
    have hd0 : d=0:=by omega
    subst d
    have hp0 : p=0:=by
      obtain ⟨c,hc,hcp⟩:=hp
      have hc0 : c=0:=funext (fun i=>Finset.sum_eq_zero_iff.mp hc i (Finset.mem_univ i))
      subst c
      change C (0 : I → ℤ)=p at hcp
      rw [map_zero] at hcp
      exact hcp.symm
    exact hv (by rw [hp0,map_zero,map_zero])
  refine ⟨p,d,hd0,hd,hp,hv,hsa,?_⟩
  intro n hn hnN m hm hm0
  have HH:=H.joint_plane hs (realRoot_mem e C N n hnN m hm) hv a hsa hm0
  apply positive_ray_of_mem_span e he C L hdeg p m d n hd0 hn hp hm
  obtain ⟨x,y,hxy⟩:=Submodule.mem_span_pair.mp HH
  apply Submodule.mem_span_singleton.mpr
  exact ⟨y,by simpa only [smul_zero,zero_add] using hxy⟩
include hdeg in
lemma section_offset_generic (N : ℕ) (v k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) 0 v k) :
    ChamberGeneric C N (k.toAddMonoidHom.comp e) := by
  intro n hn hnN m hm
  apply H.avoid _ (realRoot_mem e C N n hnN m hm)
  simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using realRoot_ne_zero C e L hdeg n hn m hm
lemma section_line_zero_not_event (N : ℕ) (v k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) 0 v k) :
    (0:ℝ)∉lineEvents (realRootsThrough e C N) v k := by
  intro hh
  obtain ⟨s,hs,hv,hs0⟩:=(mem_lineEvents_iff _ _ _ _).mp hh
  apply H.avoid s hs _
  · simpa only [zero_smul,add_zero] using hs0
  · simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using
      (show s≠0 from fun h=>hv (by rw [h,map_zero]))
lemma line_covector_add (v k : Module.Dual ℝ E) (a δ : ℝ) :
    ((k+(a+δ) • v).toAddMonoidHom.comp e)=
      (k+a • v).toAddMonoidHom.comp e+δ • (v.toAddMonoidHom.comp e) := by
  ext m
  change k (e m)+((a+δ)*v (e m))=(k (e m)+a*v (e m))+δ*v (e m)
  ring
lemma line_covector_sub (v k : Module.Dual ℝ E) (a δ : ℝ) :
    ((k+(a-δ) • v).toAddMonoidHom.comp e)=
      (k+a • v).toAddMonoidHom.comp e+δ • (-(v.toAddMonoidHom.comp e)) := by
  ext m
  change k (e m)+((a-δ)*v (e m))=(k (e m)+a*v (e m))+δ*(-v (e m))
  ring
end
end ElementaryPositivity.QuantumTorus

end

end OAI
