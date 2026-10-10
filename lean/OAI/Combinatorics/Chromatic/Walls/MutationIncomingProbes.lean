import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutationIncomingFinite
import OAI.Combinatorics.Chromatic.Walls.MutationLogCompletion

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))

omit [FiniteDimensional ℝ E] [Fintype I] in
include hS in
lemma realShearVector_ne_zero {v:E} (hv:v≠0) : realShearVector e S (simpleRoot C pc) v≠0 := by
  intro H
  have HH:=congrArg (S (e (simpleRoot C pc))) H
  simp only [realShearVector,map_add,map_smul,hS,smul_zero,add_zero,map_zero] at HH
  exact hv (by simpa only [realShearVector,HH,zero_smul,add_zero] using H)

omit [FiniteDimensional ℝ E] [Fintype I] in
include hS hcomp in
lemma incoming_side_eval (pos:Bool) (r m:M) :
    incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m=
      (S.flip (e r)) (if pos then e m else realShearVector e S (simpleRoot C pc) (e m)) := by
  cases pos
  · change (Ω m (mutationShear Ω (simpleRoot C pc) r):ℝ)=_
    rw [←hcomp]
    change S.flip (e (mutationShear Ω (simpleRoot C pc) r)) (e m)=_
    rw [←realShearCovector_incoming Ω e S (simpleRoot C pc) hS hcomp,
      realShearCovector_eval]
    rfl
  · exact (hcomp m r).symm

include he hcoord hS hcomp in
lemma mutation_incoming_probes (K N:ℕ) (r:M) (hr:e r≠0)
    (hp:e (simpleRoot C pc)∉Submodule.span ℝ {e r}) :
    ∃(pos:Bool) (x y:Module.Dual ℝ E),RegularCovector C e x ∧ RegularCovector C e y ∧
      cutSide pos (x.toAddMonoidHom.comp e) (simpleRoot C pc) ∧
      cutSide pos (y.toAddMonoidHom.comp e) (simpleRoot C pc) ∧
      (if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0) ∧
      mutationLinearPiece Ω C pc pos r=mutationIncomingLabel Ω (simpleRoot C pc) r ∧
      0<x (e r) ∧ y (e r)<0 ∧
      (∀ n≤K,∀m,HasRootDegree C n m →
        (0 < incomingCovector Ω r m → 0<x (e m) ∧ 0<y (e m)) ∧
        (incomingCovector Ω r m<0 → x (e m)<0 ∧ y (e m)<0)) ∧
      (∀ n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        (0 < incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m →
          0<realMutationCovector e S (simpleRoot C pc) x (e m) ∧
          0<realMutationCovector e S (simpleRoot C pc) y (e m)) ∧
        (incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m<0 →
          realMutationCovector e S (simpleRoot C pc) x (e m)<0 ∧
          realMutationCovector e S (simpleRoot C pc) y (e m)<0)) ∧
      (∀ n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
        realMutationCovector e S (simpleRoot C pc) x (e m)≠0 ∧
        realMutationCovector e S (simpleRoot C pc) y (e m)≠0) := by
  classical
  let A:=realRootsThrough e (mutatedRoots Ω C pc) N
  let Q:=A∪A.image (realShearVector e S (simpleRoot C pc))
  let P:=realRootsThrough e C K∪Q
  let k:=S.flip (e r)
  obtain ⟨x,y,HX,HY,Hx,Hy,hxr,hyr,hside,HS⟩:=regular_straddle_offcut C e Q P k
    (e r) (e (simpleRoot C pc)) hr (hS _) hp
  have existSide : ∃pos:Bool,(if pos then 0<x (e (simpleRoot C pc)) ∧ 0<y (e (simpleRoot C pc))
        else x (e (simpleRoot C pc))<0 ∧ y (e (simpleRoot C pc))<0):=by
    rcases hside with hh|hh
    · exact ⟨true,hh⟩
    · exact ⟨false,hh⟩
  obtain ⟨pos,hpos⟩:=existSide
  have sx : cutSide pos (x.toAddMonoidHom.comp e) (simpleRoot C pc):=by cases pos <;> exact hpos.1
  have sy : cutSide pos (y.toAddMonoidHom.comp e) (simpleRoot C pc):=by cases pos <;> exact hpos.2
  have hxside:=realMutationCovector_eq_side e S (simpleRoot C pc) pos x (by cases pos <;> exact le_of_lt hpos.1)
  have hyside:=realMutationCovector_eq_side e S (simpleRoot C pc) pos y (by cases pos <;> exact le_of_lt hpos.2)
  have evalX (m:M) : realMutationCovector e S (simpleRoot C pc) x (e m)=
      x (if pos then e m else realShearVector e S (simpleRoot C pc) (e m)):=by
    rw [hxside]; cases pos
    · exact realShearCovector_eval e S _ _ _
    · rfl
  have evalY (m:M) : realMutationCovector e S (simpleRoot C pc) y (e m)=
      y (if pos then e m else realShearVector e S (simpleRoot C pc) (e m)):=by
    rw [hyside]; cases pos
    · exact realShearCovector_eval e S _ _ _
    · rfl
  have memQ (n:ℕ) (hn:n≤N) (m:M) (hm:HasRootDegree (mutatedRoots Ω C pc) n m) :
      (if pos then e m else realShearVector e S (simpleRoot C pc) (e m))∈Q:=by
    have ha : e m∈A:=realRoot_mem e _ N n hn m hm
    cases pos
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e m,ha,rfl⟩)
    · exact Finset.mem_union_left _ ha
  have hsign : (if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0):=by
    have hs:=HS (e (simpleRoot C pc)) (Finset.mem_insert_self _ _)
    have hc : k (e (simpleRoot C pc))=(Ω (simpleRoot C pc) r:ℝ):=hcomp _ _
    cases pos
    · have hh : Ω (simpleRoot C pc) r≤0:=by
        by_contra hn
        have H:=hs.1 (by rw [hc]; exact_mod_cast lt_of_not_ge hn)
        exact (not_lt_of_ge hpos.1.le H.1)
      exact hh
    · have hh : 0≤Ω (simpleRoot C pc) r:=by
        by_contra hn
        have H:=hs.2 (by rw [hc]; exact_mod_cast lt_of_not_ge hn)
        exact (not_lt_of_ge (le_of_lt hpos.1) H.1)
      exact hh
  refine ⟨pos,x,y,HX,HY,sx,sy,hsign,?_,hxr,hyr,?_,?_,?_⟩
  · cases pos
    · exact (mutationIncomingLabel_nonpositive Ω (simpleRoot C pc) r hsign).symm
    · exact (mutationIncomingLabel_nonnegative Ω (simpleRoot C pc) r hsign).symm
  · intro n hn m hm
    have H:=HS (e m) (Finset.mem_insert_of_mem (Finset.mem_union_left _ (realRoot_mem e C K n hn m hm)))
    change ((0 < S (e m) (e r) → _) ∧ (S (e m) (e r)<0 → _)) at H
    rw [hcomp] at H
    exact H
  · intro n hn m hm
    have H:=HS _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (memQ n hn m hm)))
    rw [evalX,evalY,incoming_side_eval Ω C pc e S hS hcomp pos r m]
    exact H
  · intro n hn m hm
    have hnz : e m≠0:=by
      intro H
      have hm0 : m=0:=he (H.trans (map_zero e).symm)
      exact positive_root_ne_zero (mutatedRoots Ω C pc)
        (Function.LeftInverse.injective (mutatedCoordinates_retraction Ω C coord hcoord pc))
        (Nat.succ_pos n) (hm0 ▸ hm)
    have hv : (if pos then e m else realShearVector e S (simpleRoot C pc) (e m))≠0:=by
      cases pos
      · exact realShearVector_ne_zero C pc e S hS hnz
      · exact hnz
    rw [evalX,evalY]
    exact ⟨Hx _ (memQ (n+1) hn m hm) hv,Hy _ (memQ (n+1) hn m hm) hv⟩
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance mutationIncomingProbesRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance mutationIncomingProbesAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutationIncomingProbesAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

lemma normalizedSimple_regradeBound (δ:M →+ ℤ) (B:ℕ) (r:M) (hr:δ r=1) :
    RegradeBound LaurentRay.vUnit Ω δ (B+1) (normalizedSimple Ω r) := by
  intro n m hm
  have H:=normalizedSimple_homogeneous Ω δ r hr n m hm
  rw [H,Int.toNat_natCast]
  exact ⟨Int.natCast_nonneg _,by nlinarith⟩

omit [Fintype I] in
lemma ray_pairing_side (pos:Bool) (r:M) (i:I) (hr:OnPositiveRay r (simpleRoot C i))
    (hs:if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0) :
    if pos then 0 ≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0 := by
  obtain ⟨a,b,ha,hb,HH⟩:=hr
  have H:=congrArg (Ω (simpleRoot C pc)) HH
  simp only [map_nsmul,nsmul_eq_mul] at H
  have ha' : (0:ℤ)<a:=by exact_mod_cast ha
  have hb' : (0:ℤ)<b:=by exact_mod_cast hb
  cases pos
  · change Ω (simpleRoot C pc) r≤0 at hs
    change Ω (simpleRoot C pc) (simpleRoot C i)≤0
    nlinarith
  · change 0≤Ω (simpleRoot C pc) r at hs
    change 0≤Ω (simpleRoot C pc) (simpleRoot C i)
    nlinarith

include hcoord in
lemma mutation_literal_incoming (pos:Bool) (r:M)
    (hs:if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0)
    (ho:¬OnPositiveRay r (simpleRoot C pc))
    (hn:¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
      (simpleRoot (mutatedRoots Ω C pc) pc)) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (literalIncomingRay Ω (simpleIncomingList C) r) ∧
    mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (literalIncomingRay Ω (simpleIncomingList C) r)=
      literalIncomingRay Ω (simpleIncomingList (mutatedRoots Ω C pc)) (mutationIncomingLabel Ω (simpleRoot C pc) r) := by
  classical
  by_cases H:∃i,OnPositiveRay r (simpleRoot C i)
  · obtain ⟨i,hi⟩:=H
    have hip : i≠pc:=by rintro rfl; exact ho hi
    have hs':=ray_pairing_side Ω C pc pos r i hi hs
    have hi':= (mutationIncomingLabel_simple_ray_iff Ω C pc hΩ i hip r).mpr hi
    rw [literalIncomingRay_eq Ω _ hi,literalIncoming_simple Ω C coord hcoord i,
      literalIncomingRay_eq Ω _ hi',literalIncoming_simple Ω (mutatedRoots Ω C pc)
        (mutatedCoordinates Ω C coord pc) (mutatedCoordinates_retraction Ω C coord hcoord pc) i]
    exact ⟨normalizedSimple_regradeBound Ω _ _ _ (mutation_side_simple_order Ω C coord hcoord pc pos i hip hs'),
      mutation_normalized_simple_side Ω hΩ C coord hcoord pc pos i hip hs'⟩
  · have H':∀i,¬OnPositiveRay r (simpleRoot C i):=by simpa only [not_exists] using H
    have HH:∀i,¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
        (simpleRoot (mutatedRoots Ω C pc) i):=by
      intro i hi
      by_cases hip:i=pc
      · subst i; exact hn hi
      · exact H' i ((mutationIncomingLabel_simple_ray_iff Ω C pc hΩ i hip r).mp hi)
    rw [literalIncoming_simple_nonsimple Ω C r H',literalIncoming_simple_nonsimple Ω _ _ HH,
      mutationCompletion_one]
    exact ⟨RegradeBound.one _ _ _ _,rfl⟩

include hcoord hΩ in
lemma mutation_incoming_log_read (pos:Bool) (r:M) (d:ℕ)
    (hs:if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0)
    (ho:¬OnPositiveRay r (simpleRoot C pc))
    (hn:¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
      (simpleRoot (mutatedRoots Ω C pc) pc)) :
    coeff d (FormalLog.log (literalIncomingRay Ω (simpleIncomingList (mutatedRoots Ω C pc))
      (mutationIncomingLabel Ω (simpleRoot C pc) r))) (mutationLinearPiece Ω C pc pos r)=
      if d=(mutationNewOrder Ω C coord pc pos r).toNat then
        ∑n∈Finset.range ((mutationSize Ω C pc+1)*d+1),
          coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω r)
            (simpleTotalTransport Ω C)).val) r else 0 := by
  obtain ⟨hb,he⟩:=mutation_literal_incoming Ω hΩ C coord hcoord pc pos r hs ho hn
  rw [←he,mutationCompletion_log_read Ω hΩ C coord pc pos LaurentRay.vUnit _ hb]
  · split_ifs
    · apply Finset.sum_congr rfl
      intro n hn
      exact (literalTotalTransport_ray_prescription Ω C hΩ _ (simpleIncomingList_allowed C)
        r n r ⟨1,1,by omega,by omega,rfl⟩).symm
    · rfl
  · exact (literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) r).property.1
end
end ElementaryPositivity.QuantumTorus

end

end OAI
