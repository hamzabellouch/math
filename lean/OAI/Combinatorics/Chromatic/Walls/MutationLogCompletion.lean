import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.MutatedNegativeCharts
import OAI.Combinatorics.Chromatic.GradedAlgebra.RegradeLog

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I) (pos : Bool) (v : Rˣ)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma mutationCompletion_log (F : PowerSeries (Torus v Ω))
    (hf : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) F)
    (hc : constantCoeff F=1) :
    mutationCompletion Ω hΩ C coord pc pos v (FormalLog.log F)=
      FormalLog.log (mutationCompletion Ω hΩ C coord pc pos v F) := by
  unfold mutationCompletion
  rw [regrade_log v Ω _ _ F hf hc]
  exact (FormalLog.log_map (mutationTorusPush Ω hΩ C pc pos v).toRatAlgHom _).symm
lemma mutationCompletion_log_read (F : PowerSeries (Torus v Ω))
    (hf : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) F)
    (hc : constantCoeff F=1) (d : ℕ) (m : M) :
    coeff d (FormalLog.log (mutationCompletion Ω hΩ C coord pc pos v F))
        (mutationLinearPiece Ω C pc pos m)=
      if d=(mutationNewOrder Ω C coord pc pos m).toNat then
        ∑n∈Finset.range ((mutationSize Ω C pc+1)*d+1), coeff n (FormalLog.log F) m else 0 := by
  rw [←mutationCompletion_log Ω hΩ C coord pc pos v F hf hc,mutationCompletion_coeff_read]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedIncoming_probe (pos : Bool) (d N : ℕ) (hdN : d≤N) (r : M)
    {a b x y : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (HX : RegularCovector C e x) (HY : RegularCovector C e y)
    (hA : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      0<realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0)
    (hx : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
    (hy : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) y (e m)≠0)
    (hsx : cutSide pos (x.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hsy : cutSide pos (y.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hxo : ∀n≤(mutationSize Ω C pc+1)*d,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<x (e m)) ∧ (incomingCovector Ω r m<0 → x (e m)<0))
    (hyo : ∀n≤(mutationSize Ω C pc+1)*d,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<y (e m)) ∧ (incomingCovector Ω r m<0 → y (e m)<0))
    (hxn : ∀n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      (0 < incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m →
        0<realMutationCovector e S (simpleRoot C pc) x (e m)) ∧
      (incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m<0 →
        realMutationCovector e S (simpleRoot C pc) x (e m)<0))
    (hyn : ∀n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      (0 < incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m →
        0<realMutationCovector e S (simpleRoot C pc) y (e m)) ∧
      (incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m<0 →
        realMutationCovector e S (simpleRoot C pc) y (e m)<0))
    (hxr : 0≤x (e r)) (hyr : y (e r)<0) :
    coeff d (FormalLog.log (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (incomingCovector Ω (mutationLinearPiece Ω C pc pos r))
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val)
        (mutationLinearPiece Ω C pc pos r)=
      if d=(mutationNewOrder Ω C coord pc pos r).toNat then
        ∑n∈Finset.range ((mutationSize Ω C pc+1)*d+1),
          coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω r)
            (simpleTotalTransport Ω C)).val) r else 0 := by
  let xp:=(realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e
  let yp:=(realMutationCovector e S (simpleRoot C pc) y).toAddMonoidHom.comp e
  let T:=mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
  let F:=(negativeCovectorUnit Ω C coord hcoord pc e y*
    (negativeCovectorUnit Ω C coord hcoord pc e x)⁻¹).val.val
  have hxp : xp (mutationLinearPiece Ω C pc pos r)=x (e r):=by
    change realMutationCovector e S (simpleRoot C pc) x (e (mutationLinearPiece Ω C pc pos r))=_
    rw [realMutationCovector_eq_side e S _ pos x (by cases pos <;> exact le_of_lt hsx)]
    cases pos
    · exact realShearCovector_incidence Ω e S (simpleRoot C pc) hS hcomp x r
    · rfl
  have hyp : yp (mutationLinearPiece Ω C pc pos r)=y (e r):=by
    change realMutationCovector e S (simpleRoot C pc) y (e (mutationLinearPiece Ω C pc pos r))=_
    rw [realMutationCovector_eq_side e S _ pos y (by cases pos <;> exact le_of_lt hsy)]
    cases pos
    · exact realShearCovector_incidence Ω e S (simpleRoot C pc) hS hcomp y r
    · rfl
  have Hn:=incoming_negative_ratio_log LaurentRay.vUnit Ω (mutatedRoots Ω C pc) hΩ
    (mutationLinearPiece Ω C pc pos r) T xp yp N hxn hyn (hxp ▸ hxr) (hyp ▸ hyr) d hdN
  have Hratio:=mutatedTransport_negative_ratio Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    N HA HB HX HY hA hB hx hy
  have Hlog:=congrArg (fun f:Torus LaurentRay.vUnit Ω=>f (mutationLinearPiece Ω C pc pos r))
    (FormalLog.log_coeff_congr _ _ d (fun j hj=>Hratio j (hj.trans hdN)))
  have Hcut:=mutatedTransport_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd pos HX HY hsx hsy
  have hc : constantCoeff F=1:=by
    change constantCoeff ((chartNegative LaurentRay.vUnit Ω C (y.toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val * invOfUnit (chartNegative LaurentRay.vUnit Ω C
          (x.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val 1)=1
    simp only [map_mul,(chartNegative LaurentRay.vUnit Ω C _ (simpleTotalTransport Ω C)).property.1,
      constantCoeff_invOfUnit,inv_one,Units.val_one,one_mul]
  have Ho:=incoming_negative_ratio_log LaurentRay.vUnit Ω C hΩ r (simpleTotalTransport Ω C)
    (x.toAddMonoidHom.comp e) (y.toAddMonoidHom.comp e) ((mutationSize Ω C pc+1)*d) hxo hyo hxr hyr
  rw [←Hn,←Hlog,Hcut.2,mutationCompletion_log_read Ω hΩ C coord pc pos LaurentRay.vUnit F Hcut.1 hc]
  split_ifs
  · apply Finset.sum_congr rfl
    intro j hj
    exact Ho j (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj)
  · rfl
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
attribute [local instance] Classical.decEq
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
lemma regular_covector_with_signs (Q P : Finset E) (k : Module.Dual ℝ E) :
    ∃h : Module.Dual ℝ E,RegularCovector C e h ∧ (∀q∈Q,q≠0 → h q≠0) ∧
      ∀s∈P,(0<k s → 0<h s) ∧ (k s<0 → h s<0) := by
  classical
  let W : Set E:=((⋃N,(realRootsThrough e C N : Set E))∪(Q : Set E))\{0}
  have hW : W.Countable:=
    ((Set.countable_iUnion (fun N=>(realRootsThrough e C N).countable_toSet)).union Q.countable_toSet).mono
      Set.sdiff_subset
  have hp : ∀w∈W,w∉Submodule.span ℝ ({0}:Set E):=by
    intro w hw
    simpa only [W,Set.mem_sdiff,Set.mem_singleton_iff,Submodule.span_zero_singleton,Submodule.mem_bot]
      using hw.2
  obtain ⟨h,_,hh,HS⟩:=countable_avoid_with_probes W hW 0 hp
    (P.image (fun s=>(0,s))) 0 k (map_zero k)
  refine ⟨h,?_,?_,?_⟩
  · intro N s hs hn
    exact hh s ⟨Or.inl (Set.mem_iUnion.mpr ⟨N,hs⟩),hn⟩
  · intro q hq hn
    exact hh q ⟨Or.inr hq,hn⟩
  · intro s hs
    simpa only [zero_smul,add_zero] using HS (0,s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)

lemma regular_straddle (Q P : Finset E) (k : Module.Dual ℝ E) (r : E)
    (hr : r≠0) (hk : k r=0) :
    ∃x y : Module.Dual ℝ E,RegularCovector C e x ∧ RegularCovector C e y ∧
      (∀q∈Q,q≠0 → x q≠0) ∧ (∀q∈Q,q≠0 → y q≠0) ∧
      0<x r ∧ y r<0 ∧
      ∀s∈P,(0<k s → 0<x s ∧ 0<y s) ∧ (k s<0 → x s<0 ∧ y s<0) := by
  classical
  obtain ⟨g,hg⟩:=Module.Projective.exists_dual_eq_one ℝ hr
  obtain ⟨ε,hε,HE⟩:=preserve_finite_signs P k g
  obtain ⟨η,hη,HH⟩:=preserve_finite_signs P k (-g)
  let kx:=k+(ε/2) • g
  let ky:=k+(η/2) • (-g)
  obtain ⟨x,HX,Hx,Sx⟩:=regular_covector_with_signs C e Q (insert r P) kx
  obtain ⟨y,HY,Hy,Sy⟩:=regular_covector_with_signs C e Q (insert r P) ky
  have hxr : 0<kx r:=by simp only [kx,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hk,hg]; linarith
  have hyr : ky r<0:=by simp only [ky,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.neg_apply,smul_eq_mul,hk,hg]; linarith
  refine ⟨x,y,HX,HY,Hx,Hy,(Sx r (Finset.mem_insert_self _ _)).1 hxr,
    (Sy r (Finset.mem_insert_self _ _)).2 hyr,?_⟩
  intro s hs
  have He:=HE (ε/2) (by linarith) (by linarith) s hs
  have Hh:=HH (η/2) (by linarith) (by linarith) s hs
  exact ⟨fun h=>⟨(Sx s (Finset.mem_insert_of_mem hs)).1 (He.1 h),
      (Sy s (Finset.mem_insert_of_mem hs)).1 (Hh.1 h)⟩,
    fun h=>⟨(Sx s (Finset.mem_insert_of_mem hs)).2 (He.2.1 h),
      (Sy s (Finset.mem_insert_of_mem hs)).2 (Hh.2.1 h)⟩⟩

lemma regular_straddle_offcut (Q P : Finset E) (k : Module.Dual ℝ E) (r p : E)
    (hr : r≠0) (hk : k r=0) (hp : p∉Submodule.span ℝ {r}) :
    ∃x y : Module.Dual ℝ E,RegularCovector C e x ∧ RegularCovector C e y ∧
      (∀q∈Q,q≠0 → x q≠0) ∧ (∀q∈Q,q≠0 → y q≠0) ∧
      0<x r ∧ y r<0 ∧ ((0<x p ∧ 0<y p) ∨ (x p<0 ∧ y p<0)) ∧
      ∀s∈insert p P,(0<k s → 0<x s ∧ 0<y s) ∧ (k s<0 → x s<0 ∧ y s<0) := by
  classical
  obtain ⟨h,hhr,hhp,Hh⟩:=generic_offset r {p} (insert p P) k hk (by simpa using hp)
  obtain ⟨x,y,HX,HY,Hx,Hy,hxr,hyr,HS⟩:=regular_straddle C e Q (insert p P) h r hr hhr
  refine ⟨x,y,HX,HY,Hx,Hy,hxr,hyr,?_,?_⟩
  · rcases lt_or_gt_of_ne (hhp p (Finset.mem_singleton_self p)) with hn|hn
    · exact Or.inr ((HS p (Finset.mem_insert_self _ _)).2 hn)
    · exact Or.inl ((HS p (Finset.mem_insert_self _ _)).1 hn)
  · intro s hs
    exact ⟨fun h=>(HS s hs).1 ((Hh s hs).1 h),fun h=>(HS s hs).2 ((Hh s hs).2 h)⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
