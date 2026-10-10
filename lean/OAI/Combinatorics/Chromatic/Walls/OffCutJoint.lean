import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PlanarRefinement
import OAI.Combinatorics.Chromatic.Walls.NonpJoint
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationCoordinates

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))

def cutSide (pos : Bool) (h : M →+ ℝ) (p : M) : Prop := if pos then 0<h p else h p<0

lemma simpleRoot_degree : HasRootDegree C 1 (simpleRoot C pc) := by
  refine ⟨Pi.single pc 1,by simp,?_⟩
  congr 1
  ext i
  by_cases hi : i=pc
  · subst i; simp
  · simp [hi]

include hcoord he hB hcomp hdeg in
lemma offcut_planar_support (N : ℕ) (hN : 0<N) (n : ℤ) (P : AddSubmonoid M)
    (pos : Bool) (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (s : E) (hrs : B (e r) s≠0) (k : Module.Dual ℝ E)
    (hkr : k (e r)=0) (hks : k s=0)
    (hzero : ∀d,d≤N → ∀m,HasRootDegree C d m → k (e m)=0 → e m∈Submodule.span ℝ {e r,s})
    (hside : cutSide pos (k.toAddMonoidHom.comp e) (simpleRoot C pc))
    (F : CompletedPositive v Ω C)
    (HI : ∀q d,0<d → HasRootDegree C d q → ∀h : Module.Dual ℝ E,
      RayGeneric C N q (h.toAddMonoidHom.comp e) →
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero v Ω C (h.toAddMonoidHom.comp e) F).val m≠0 →
        nonpDegree coord pc m<n → m∈P)
    (HR : ∀j≤N,∀m,
      coeff j (chartZero v Ω C (incomingCovector Ω r)
        (chartZero v Ω C (k.toAddMonoidHom.comp e) F)).val m≠0 →
      nonpDegree coord pc m=n → m∈P) :
    ∀j≤N,∀m,
      coeff j (chartZero v Ω C (-incomingCovector Ω r)
        (chartZero v Ω C (k.toAddMonoidHom.comp e) F)).val m≠0 →
      nonpDegree coord pc m=n → m∈P := by
  classical
  let kM:=k.toAddMonoidHom.comp e
  let J:=chartZero v Ω C kM F
  let Jc:=completedCut v Ω C N J
  let w:=nonpDegree coord pc
  let h:=incomingCovector Ω r
  let Q:=nonpSupportFrame w h P n
  have hp : kM (simpleRoot C pc)≠0:=by
    cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hside
    · exact ne_of_lt hside
    · exact ne_of_gt hside
  have hker : ∀j,coeff j Jc.val∈supportedSubring v Ω kM.ker.toAddSubmonoid:=
    completedCut_supported v Ω C N J _ (fun j _=>chartZero_supported_kernel v Ω C kM F j)
  have hplane : ∀j,coeff j Jc.val∈supportedSubring v Ω (planeRoots e (e r) s):=by
    apply completedCut_supported v Ω C N J _
    intro j hj m hm
    by_contra hval
    have hmroot:=chart_root_of_ne v Ω C J j m hval
    have hmz : kM m=0:=by
      by_contra HH; exact hval (chartZero_supported_kernel v Ω C kM F j m HH)
    exact hm (hzero j hj m hmroot hmz)
  have hcut (a : M →+ ℝ) : ∀j≤N,coeff j (chartZero v Ω C a Jc).val=coeff j (chartZero v Ω C a J).val:=by
    apply chartZero_congr_through v Ω C a Jc J N
    exact fun j hj=>coeff_cut_of_le J.val hj
  have hrootpos (q : M) (j : ℕ) (hj : 0<j) (m : M)
      (hm : coeff j (chartZero v Ω C (incomingCovector Ω q) Jc).val m≠0) : 0<w m:=by
    apply nonp_positive_off_cut C coord hcoord pc hj
      (chart_root_of_ne v Ω C _ j m hm) kM hp
    by_contra HH
    exact hm ((chartThree_supported v Ω C (incomingCovector Ω q) kM.ker.toAddSubmonoid Jc hker).2.1 j m HH)
  have htargeteq : ∀q d,0<d → HasRootDegree C d q → q∈planeRoots e (e r) s →
      Ω q r=0 → chartZero v Ω C (incomingCovector Ω q) Jc=chartZero v Ω C h Jc:=by
    intro q d hd hdq hqP hqr
    have hqr' : OnPositiveRay r q:=positive_ray_of_pairing_zero e he B hB L (e r) s C hdeg hrs
      q r d dr hd hdr hdq hrd hqP (Submodule.subset_span (by simp)) (by rw [hcomp,hqr,Int.cast_zero])
    exact (incoming_same_ray v Ω C hqr' Jc).symm
  have hhIncoming : ∀q d,0<d → d≤N → HasRootDegree C d q → q∈planeRoots e (e r) s →
      ∀j≤N,coeff j (chartZero v Ω C (incomingCovector Ω q) Jc).val∈supportedSubring v Ω Q:=by
    intro q d hd hdN hdq hqP j hj m hmQ
    by_contra hval
    have hm0 : m≠0:=by intro hh; exact hmQ (hh ▸ Q.zero_mem)
    have hj0 : 0<j:=by
      by_contra hh
      have hjz : j=0:=by omega
      subst j
      rw [coeff_zero_eq_constantCoeff,(chartZero v Ω C (incomingCovector Ω q) Jc).property.1] at hval
      exact hval (Finsupp.single_eq_of_ne hm0)
    apply hmQ
    refine Or.inr ⟨hrootpos q j hj0 m hval,?_⟩
    intro hw
    rcases hw with hw | ⟨hw,hh⟩
    · obtain ⟨η,hη,Hη⟩:=planar_refinement_generic v Ω C e he B hB hcomp L hdeg N
        (e r) s hrs k hkr hks hzero q d hd hdq hqP F
      obtain ⟨ε,hε,Hε⟩:=root_lex_epsilon C N kM (incomingCovector Ω q)
      let δ:=min η ε/2
      have hδ : 0<δ:=by dsimp [δ]; positivity
      have hδη : δ<η:=by dsimp [δ]; have := min_le_left η ε; linarith [lt_min hη hε]
      have hδε : δ<ε:=by dsimp [δ]; have := min_le_right η ε; linarith [lt_min hη hε]
      obtain ⟨hgen,HRef⟩:=Hη δ hδ hδη
      have hsign:=Hε δ hδ hδε 1 hN (simpleRoot C pc) (simpleRoot_degree C pc)
      have hside' : cutSide pos ((k+δ • B.flip (e q)).toAddMonoidHom.comp e) (simpleRoot C pc):=by
        rw [real_perturbed_covector Ω e B hcomp]
        cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hside ⊢
        · exact hsign.2.1 hside
        · exact hsign.1 hside
      apply HI q d hd hdq _ hgen hside' j hj m ?_ hw
      rw [HRef j hj,←hcut _ j hj]
      exact hval
    · have hmroot:=chart_root_of_ne v Ω C _ j m hval
      have hmP : m∈planeRoots e (e r) s:=by
        by_contra HH
        exact hval ((chartThree_supported v Ω C (incomingCovector Ω q) (planeRoots e (e r) s) Jc hplane).2.1 j m HH)
      have hmqr : B (e m) (e q)=0:=by
        rw [hcomp]
        have HK:=chartZero_supported_kernel v Ω C (incomingCovector Ω q) Jc j
        by_contra HH
        exact hval (HK m HH)
      have hqm : OnPositiveRay q m:=positive_ray_of_pairing_zero e he B hB L (e r) s C hdeg hrs
        m q j d hj0 hd hmroot hdq hmP hqP hmqr
      have hqr : Ω q r=0:=by
        have HH:=(hqm.eval h).2.1.mp hh
        change (Ω q r:ℝ)=0 at HH
        exact_mod_cast HH
      have hhEq:=htargeteq q d hd hdq hqP hqr
      rw [hhEq,hcut h j hj] at hval
      exact HR j hj m hval hw
  have hQ:=planar_joint_support v Ω C e he B hB hcomp L hdeg (e r) s
    (by rw [hdeg dr r hrd]; exact_mod_cast hdr) hrs Jc hplane N Q hhIncoming (-h)
  intro j hj m hval hw
  apply nonpSupportFrame_target (w:=w) (h:=h) (n:=n) (m:=m) (P:=P) ?_ hw ?_
  · by_contra HH
    have Hzero:=hQ j hj m HH
    rw [hcut (-h) j hj] at Hzero
    exact hval Hzero
  · have HK:=chartZero_supported_kernel v Ω C (-h) J j
    have Hneg : (-h) m=0:=by by_contra HH; exact hval (HK m HH)
    simpa only [AddMonoidHom.neg_apply,neg_eq_zero] using Hneg
end
end ElementaryPositivity.QuantumTorus

end

end OAI
