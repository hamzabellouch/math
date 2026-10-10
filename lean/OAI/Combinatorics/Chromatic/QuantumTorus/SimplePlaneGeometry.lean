import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PureCutFactorization

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
include he hB hcomp in
lemma plane_lattice_relation (p r q : M) (hq : e q∈Submodule.span ℝ {e p,e r}) :
    (Ω p r) • q=(Ω q r) • p+(Ω p q) • r := by
  apply he
  rw [map_zsmul,map_add,map_zsmul,map_zsmul]
  simp only [←Int.cast_smul_eq_zsmul ℝ]
  rw [←hcomp,←hcomp,←hcomp]
  obtain ⟨a,b,hq⟩:=Submodule.mem_span_pair.mp hq
  rw [←hq]
  simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,hB,
    mul_zero,zero_add,add_zero,smul_add,smul_smul]
  congr 1 <;> congr 1 <;> ring
include hcoord he hB hcomp in
lemma plane_nonp_relation (r q : M) (hq : q∈planeRoots e (e (simpleRoot C pc)) (e r)) :
    Ω (simpleRoot C pc) r*nonpDegree coord pc q=
      Ω (simpleRoot C pc) q*nonpDegree coord pc r := by
  have H:=congrArg (nonpDegree coord pc)
    (plane_lattice_relation Ω e he B hB hcomp (simpleRoot C pc) r q hq)
  simpa only [map_add,map_zsmul,smul_eq_mul,nonpDegree_simple_self C coord hcoord,mul_zero,zero_add] using H
include hcoord he hB hcomp in
lemma plane_simple_pairing_sign (pos : Bool) (r q : M)
    (hr : 0<nonpDegree coord pc r)
    (htrend : 0<sideSign pos*Ω (simpleRoot C pc) r)
    (hq : q∈planeRoots e (e (simpleRoot C pc)) (e r)) :
    (0≤nonpDegree coord pc q → 0≤ sideSign pos*Ω (simpleRoot C pc) q) ∧
    (0<nonpDegree coord pc q → 0<sideSign pos*Ω (simpleRoot C pc) q) ∧
    (nonpDegree coord pc q=0 ↔ Ω (simpleRoot C pc) q=0) := by
  have H:=plane_nonp_relation Ω C coord hcoord pc e he B hB hcomp r q hq
  have HE : (sideSign pos*Ω (simpleRoot C pc) r)*nonpDegree coord pc q=
      (sideSign pos*Ω (simpleRoot C pc) q)*nonpDegree coord pc r:=by
    calc
      _=sideSign pos*(Ω (simpleRoot C pc) r*nonpDegree coord pc q):=by ring
      _=sideSign pos*(Ω (simpleRoot C pc) q*nonpDegree coord pc r):=by rw [H]
      _=_:=by ring
  refine ⟨fun hh=>by nlinarith,fun hh=>by nlinarith,?_⟩
  have ht : Ω (simpleRoot C pc) r≠0:=by intro hz; rw [hz,mul_zero] at htrend; omega
  constructor
  · intro hh
    rw [hh,mul_zero] at H
    exact (mul_eq_zero.mp H.symm).resolve_right (ne_of_gt hr)
  · intro hh
    rw [hh,zero_mul] at H
    exact (mul_eq_zero.mp H).resolve_left ht
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hB hcomp hdeg in
lemma cut_planar_fiber (N : ℕ) (n : ℤ) (pos : Bool)
    (r : M) (hr : 0<nonpDegree coord pc r)
    (ht : 0<sideSign pos*Ω (simpleRoot C pc) r)
    (k : Module.Dual ℝ E) (hkp : k (e (simpleRoot C pc))=0) (hkr : k (e r)=0)
    (hzero : ∀j,j≤N → ∀m,HasRootDegree C j m → k (e m)=0 →
      m∈planeRoots e (e (simpleRoot C pc)) (e r))
    (HU : ∀q d,0<d → HasRootDegree C d q →
      0<sideSign pos*Ω (simpleRoot C pc) q → ∀h : Module.Dual ℝ E,
      RayGeneric C N q (h.toAddMonoidHom.comp e) →
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m≤n →
        m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (-incomingCovector Ω r)
      (chartZero LaurentRay.vUnit Ω C (k.toAddMonoidHom.comp e) (simpleTotalTransport Ω C))).val m≠0 →
      nonpDegree coord pc m≤n →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (-sideSign pos) := by
  classical
  let p:=simpleRoot C pc
  let F:=simpleTotalTransport Ω C
  let kM:=k.toAddMonoidHom.comp e
  let J:=chartZero LaurentRay.vUnit Ω C kM F
  let Jc:=completedCut LaurentRay.vUnit Ω C N J
  let P:=fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)
  let Q:=boundedNonpFrame (nonpDegree coord pc) P n
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have H:=hB (e m); rw [hcomp] at H; exact_mod_cast H
  have hpr : B (e p) (e r)≠0:=by
    rw [hcomp]
    intro hz
    have hz' : Ω p r=0:=by exact_mod_cast hz
    change 0<sideSign pos*Ω p r at ht
    rw [hz',mul_zero] at ht; omega
  have hplane : ∀j,coeff j Jc.val∈supportedSubring LaurentRay.vUnit Ω (planeRoots e (e p) (e r)):=by
    apply completedCut_supported
    intro j hj m hm
    by_contra hv
    have hz : kM m=0:=by
      by_contra hh; exact hv (chartZero_supported_kernel LaurentRay.vUnit Ω C kM F j m hh)
    exact hm (hzero j hj m (chart_root_of_ne LaurentRay.vUnit Ω C J j m hv) hz)
  obtain ⟨l,hl,hpair,hRay,hfact⟩:=planar_joint_factorization LaurentRay.vUnit Ω C e he B hB hcomp
    L hdeg (e p) (e r) (by rw [hdeg 1 p (simpleRoot_degree C pc)]; norm_num) hpr Jc hplane N
  let K (q : M):=completedCut LaurentRay.vUnit Ω C N (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω q) Jc)
  let lA:=l.filter (fun q=>decide (nonpDegree coord pc q≠0))
  let A:=completedListProduct LaurentRay.vUnit Ω C lA K
  have hcut (a : M →+ ℝ) : ∀j≤N,coeff j (chartZero LaurentRay.vUnit Ω C a Jc).val=
      coeff j (chartZero LaurentRay.vUnit Ω C a J).val:=
    chartZero_congr_through LaurentRay.vUnit Ω C a Jc J N (fun j hj=>coeff_cut_of_le J.val hj)
  have hKray : ∀q∈l,∀j m,coeff (j+1) (K q).val m≠0 → OnPositiveRay q m:=by
    intro q hq j m hm
    change coeff (j+1) (cut N (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω q) Jc).val) m≠0 at hm
    rw [coeff_cut] at hm
    split_ifs at hm with hj
    · exact hRay q hq j hj m hm
    · exact False.elim (hm rfl)
  have hltrend : ∀q∈l,0≤ sideSign pos*Ω p q:=by
    intro q hq
    obtain ⟨d,hd,hdN,hdq,hqP⟩:=hl q hq
    exact (plane_simple_pairing_sign Ω C coord hcoord pc e he B hB hcomp pos r q hr ht hqP).1
      (nonpDegree_root_nonneg C coord hcoord pc hdq)
  have hAframe : ∀j,coeff j A.val∈supportedSubring LaurentRay.vUnit Ω Q:=by
    apply completed_list_supported
    intro q hq
    have hq':=List.mem_filter.mp hq
    obtain ⟨d,hd,hdN,hdq,hqP⟩:=hl q hq'.1
    have hnq : 0<nonpDegree coord pc q:=lt_of_le_of_ne
      (nonpDegree_root_nonneg C coord hcoord pc hdq) (Ne.symm (of_decide_eq_true hq'.2))
    have htq:=(plane_simple_pairing_sign Ω C coord hcoord pc e he B hB hcomp pos r q hr ht hqP).2.1 hnq
    apply completedCut_supported
    intro j hj m hmQ
    by_contra hv
    apply hmQ
    refine ⟨nonpDegree_root_nonneg C coord hcoord pc
      (chart_root_of_ne LaurentRay.vUnit Ω C _ j m hv),?_⟩
    intro hn
    obtain ⟨ε,hε,Hε⟩:=planar_refinement_generic LaurentRay.vUnit Ω C e he B hB hcomp L hdeg
      N (e p) (e r) hpr k hkp hkr hzero q d hd hdq hqP F
    obtain ⟨hg,heq⟩:=Hε (ε/2) (by positivity) (by linarith)
    apply HU q d hd hdq htq _ hg ?_ j hj m ?_ hn
    · rw [real_perturbed_covector Ω e B hcomp]
      have hev : (kM+(ε/2) • incomingCovector Ω q) p=(ε/2)*(Ω p q:ℝ):=by
        change k (e p)+(ε/2)*(Ω p q:ℝ)=_; rw [hkp,zero_add]
      cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] <;> rw [hev]
      · have hh : (Ω p q:ℝ)<0:=by
          have : Ω p q<0:=by simpa [sideSign] using htq
          exact_mod_cast this
        exact mul_neg_of_pos_of_neg (by positivity) hh
      · have hh : 0<(Ω p q:ℝ):=by
          have : 0<Ω p q:=by simpa [sideSign] using htq
          exact_mod_cast this
        exact mul_pos (by positivity) hh
    · rw [heq j hj,←hcut _ j hj]; exact hv
  have hAplane : ∀j,coeff j A.val∈supportedSubring LaurentRay.vUnit Ω (planeRoots e (e p) (e r)):=by
    apply completed_list_supported
    intro q hq
    apply completedCut_supported
    intro j hj
    exact (chartThree_supported LaurentRay.vUnit Ω C (incomingCovector Ω q) _ Jc hplane).2.1 j
  have hAtrend : ∀j≤N,∀m,coeff j A.val m≠0 → 0≤ sideSign pos*Ω p m:=by
    intro j hj m hm
    have hmP : m∈planeRoots e (e p) (e r):=by by_contra hh; exact hm (hAplane j m hh)
    exact (plane_simple_pairing_sign Ω C coord hcoord pc e he B hB hcomp pos r m hr ht hmP).1
      (nonpDegree_root_nonneg C coord hcoord pc (chart_root_of_ne LaurentRay.vUnit Ω C A j m hm))
  have hface : ∀j≤N,coeff j (pureFace Ω C coord pc Jc).val=
      coeff j (simpleCompleted Ω C coord hcoord pc).val:=by
    intro j hj
    change coeff j (pureFaceSeries Ω coord pc Jc.val)=_
    rw [coeff_pureFaceSeries]
    change zeroProject LaurentRay.vUnit Ω (pureFaceCovector coord pc) (coeff j (cut N J.val))=_
    rw [coeff_cut_of_le J.val hj,←coeff_pureFaceSeries]
    change coeff j (pureFace Ω C coord pc J).val=_
    rw [pureFace_chartZero Ω C coord hcoord pc kM hkp F,pureFace_simpleTransport_value Ω C coord hcoord pc hΩ]
    rfl
  have hprod : ∀j≤N,coeff j Jc.val=coeff j
      (if pos then (normalizedSimple Ω p)*A.val else A.val*(normalizedSimple Ω p)):=by
    apply ordered_pure_factor_through Ω C coord hcoord pc hΩ pos l K hpair
      (fun q hq=>by obtain ⟨d,hd,_,hr,_⟩:=hl q hq; exact ⟨d,hd,hr⟩) hltrend hKray
      Jc (simpleCompleted Ω C coord hcoord pc) N ?_ hface
    intro j hj
    refine (hfact j hj).trans ?_
    exact completedListProduct_congr_through LaurentRay.vUnit Ω C l _ K N
      (fun q _ a ha=>(coeff_cut_of_le _ ha).symm) j hj
  have hside : cutSide (!pos) (-incomingCovector Ω r) p:=by
    cases pos <;> simp only [cutSide,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false,
      AddMonoidHom.neg_apply,incomingCovector] <;>
      norm_num only [Int.cast_neg,neg_pos,neg_lt_zero]
    · have H : Ω p r<0:=by simpa [sideSign] using ht
      change (Ω p r:ℝ)<0
      exact_mod_cast H
    · have H : 0<Ω p r:=by simpa [sideSign] using ht
      change 0<(Ω p r:ℝ)
      exact_mod_cast H
  have HB:=simple_cut_chart_bound Ω C coord hcoord pc hΩ pos A Jc N n hprod hAtrend
    (by
      intro j hj m hm hn
      have H : m∈Q:=by by_contra hh; exact hm (hAframe j m hh)
      exact H.2 hn)
    (-incomingCovector Ω r) hside
  intro j hj m hm hn
  exact HB j hj m (by rwa [hcut _ j hj]) hn
end
end ElementaryPositivity.QuantumTorus

end

end OAI
