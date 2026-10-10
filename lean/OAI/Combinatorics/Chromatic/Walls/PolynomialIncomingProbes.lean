import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PolynomialIncomingPerturbation
import OAI.Combinatorics.Chromatic.QuantumTorus.NearCutPolynomialSeeds

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
include hS hcomp in
lemma polynomial_incoming_probes (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (r:M) (K N:ℕ) :
    ∃pos:Bool,∃h:Module.Dual ℝ E,RegularCovector C e h ∧
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) ∧
      mutationLinearPiece Ω C pc pos r=mutationIncomingLabel Ω (simpleRoot C pc) r ∧
      (∀n≤K,∀m,HasRootDegree C n m →
        (0 < incomingCovector Ω r m → 0<h (e m)) ∧
        (incomingCovector Ω r m<0 → h (e m)<0)) ∧
      (∀n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        (0 < incomingCovector Ω (mutationIncomingLabel Ω (simpleRoot C pc) r) m →
          0<realMutationCovector e S (simpleRoot C pc) h (e m)) ∧
        (incomingCovector Ω (mutationIncomingLabel Ω (simpleRoot C pc) r) m<0 →
          realMutationCovector e S (simpleRoot C pc) h (e m)<0)) ∧
      (∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        realMutationCovector e S (simpleRoot C pc) h (e m)≠0) := by
  classical
  let A:=realRootsThrough e (mutatedRoots Ω C pc) N
  let Q:=A∪A.image (realShearVector e S (simpleRoot C pc))
  let P:=insert (e (simpleRoot C pc)) (realRootsThrough e C K∪Q)
  let T:ℕ → Finset E:=fun d=>realRootsThrough e C d∪
    (realRootsThrough e (mutatedRoots Ω C pc) d∪
      (realRootsThrough e (mutatedRoots Ω C pc) d).image (realShearVector e S (simpleRoot C pc)))
  let k:=S.flip (e r)
  obtain ⟨h,Ha,_,HP⟩:=generic_for_two_directions_with_probes T 0 0 k (P.image (fun x=>(0,x))) 0
  have HS:∀x∈P,(0<k x → 0<h x) ∧ (k x<0 → h x<0):=by
    intro x hx
    simpa only [zero_smul,add_zero] using HP (0,x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  have Hreg:RegularCovector C e h:=by
    intro d s hs hn
    exact (Ha d).avoid s (Finset.mem_union_left _ hs)
      (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  have hp0:e (simpleRoot C pc)≠0:=hC.ne_zero pc
  have hhp:h (e (simpleRoot C pc))≠0:=Hreg 1 _
    (realRoot_mem e C 1 1 le_rfl _ (simpleRoot_degree C pc)) hp0
  obtain ⟨pos,hpos⟩:∃pos:Bool,cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc):=by
    rcases lt_or_gt_of_ne hhp with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have heval(m:M):realMutationCovector e S (simpleRoot C pc) h (e m)=
      h (if pos then e m else realShearVector e S (simpleRoot C pc) (e m)):=by
    rw [realMutationCovector_eq_side e S _ pos h (by cases pos <;> exact le_of_lt hpos)]
    cases pos
    · exact realShearCovector_eval e S _ _ _
    · rfl
  have hsign:(if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0):=by
    have hs:=HS _ (Finset.mem_insert_self _ _)
    have hc:k (e (simpleRoot C pc))=(Ω (simpleRoot C pc) r:ℝ):=hcomp _ _
    cases pos
    · change h (e (simpleRoot C pc))<0 at hpos
      by_contra hn
      have H:=hs.1 (by rw [hc]; exact_mod_cast lt_of_not_ge hn)
      linarith
    · change 0<h (e (simpleRoot C pc)) at hpos
      by_contra hn
      have H:=hs.2 (by rw [hc]; exact_mod_cast lt_of_not_ge hn)
      linarith
  have hlabel:mutationLinearPiece Ω C pc pos r=mutationIncomingLabel Ω (simpleRoot C pc) r:=by
    cases pos
    · exact (mutationIncomingLabel_nonpositive Ω _ r hsign).symm
    · exact (mutationIncomingLabel_nonnegative Ω _ r hsign).symm
  refine ⟨pos,h,Hreg,hpos,hlabel,?_,?_,?_⟩
  · intro n hn m hm
    have H:=HS _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (realRoot_mem e C K n hn m hm)))
    change (0<S (e m) (e r) → _) ∧ (S (e m) (e r)<0 → _) at H
    rw [hcomp] at H
    exact H
  · intro n hn m hm
    have HA:e m∈A:=realRoot_mem e _ N n hn m hm
    have HQ:(if pos then e m else realShearVector e S (simpleRoot C pc) (e m))∈Q:=by
      cases pos
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e m,HA,rfl⟩)
      · exact Finset.mem_union_left _ HA
    have H:=HS _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ HQ))
    rw [←hlabel,incoming_side_eval Ω C pc e S hS hcomp pos r m,heval]
    exact H
  · intro n hn m hm
    obtain ⟨J,hJ⟩:=mutated_degree_covector Ω C pc e hC
    have hm0:e m≠0:=by
      have H:=covector_root_pos (mutatedRoots Ω C pc) e J (fun i=>by rw [hJ]; norm_num) hn hm
      intro hh
      rw [hh,map_zero] at H
      exact lt_irrefl _ H
    have hv:(if pos then e m else realShearVector e S (simpleRoot C pc) (e m))≠0:=by
      cases pos
      · exact realShearVector_ne_zero C pc e S hS hm0
      · exact hm0
    have HT:(if pos then e m else realShearVector e S (simpleRoot C pc) (e m))∈T n:=by
      apply Finset.mem_union_right
      have HH:=realRoot_mem e (mutatedRoots Ω C pc) n n le_rfl m hm
      cases pos
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e m,HH,rfl⟩)
      · exact Finset.mem_union_left _ HH
    rw [heval]
    exact (Ha n).avoid _ HT (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hv)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)
include he hdeg hS hcomp hnd in
lemma polynomialSectionIncoming_mutation (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (r:M) :
    polynomialSectionIncoming Ω C coord F r=
      polynomialSectionIncoming Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc) F'
        (mutationIncomingLabel Ω (simpleRoot C pc) r) := by
  obtain ⟨pos,h,Hreg,hs,hl,ho,hn,Hnew⟩:=polynomial_incoming_probes Ω C pc e S hS hcomp hC r
    (polynomialSectionOrderBound Ω coord F r)
    (polynomialSectionOrderBound Ω (mutatedCoordinates Ω C coord pc) F'
      (mutationIncomingLabel Ω (simpleRoot C pc) r))
  have Hold:=polynomialSection_incoming_perturbation Ω hΩ C coord F r (h.toAddMonoidHom.comp e) ho
  have Hnew':=polynomialSection_incoming_perturbation Ω hΩ (mutatedRoots Ω C pc)
    (mutatedCoordinates Ω C coord pc) F' (mutationIncomingLabel Ω (simpleRoot C pc) r)
    ((realMutationCovector e S (simpleRoot C pc) h).toAddMonoidHom.comp e) hn
  rw [←Hold,←Hnew',←hl]
  exact (polynomialSection_mutation Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC F F' hF
    pos h Hreg hs Hnew r).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
