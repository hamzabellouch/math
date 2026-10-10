import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteRayGeometry

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry RootTruncation
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hcomp in
lemma real_incoming_covector (p : M) :
    (B.flip (e p)).toAddMonoidHom.comp e=incomingCovector Ω p := by
  ext m
  exact hcomp m p
include hcomp in
lemma real_perturbed_covector (k : Module.Dual ℝ E) (p : M) (δ : ℝ) :
    (k+δ • B.flip (e p)).toAddMonoidHom.comp e=
      k.toAddMonoidHom.comp e+δ • incomingCovector Ω p := by
  ext m
  change k (e m)+δ*B (e m) (e p)=k (e m)+δ*(Ω m p:ℝ)
  rw [hcomp]
lemma linear_zero_on_plane (k : Module.Dual ℝ E) (r s m : E)
    (hr : k r=0) (hs : k s=0) (hm : m∈Submodule.span ℝ {r,s}) : k m=0 := by
  obtain ⟨a,b,rfl⟩:=Submodule.mem_span_pair.mp hm
  simp only [map_add,map_smul,hr,hs,smul_zero,add_zero]
omit [Algebra ℚ R] in
include he hB hcomp hdeg in
lemma planar_refinement_generic (N : ℕ) (r s : E) (hrs : B r s≠0)
    (k : Module.Dual ℝ E) (hkr : k r=0) (hks : k s=0)
    (hzero : ∀n,n ≤ N → ∀m,HasRootDegree C n m → k (e m)=0 → e m∈Submodule.span ℝ {r,s})
    (p : M) (d : ℕ) (hd : 0 < d) (hp : HasRootDegree C d p)
    (hpP : e p∈Submodule.span ℝ {r,s}) (F : CompletedPositive v Ω C) :
    ∃ε > 0,∀δ : ℝ,0 < δ → δ < ε →
      RayGeneric C N p ((k+δ • B.flip (e p)).toAddMonoidHom.comp e) ∧
      ∀n ≤ N,coeff n (chartZero v Ω C ((k+δ • B.flip (e p)).toAddMonoidHom.comp e) F).val=
        coeff n (chartZero v Ω C (incomingCovector Ω p)
          (chartZero v Ω C (k.toAddMonoidHom.comp e) F)).val := by
  let kM:=k.toAddMonoidHom.comp e
  obtain ⟨ε,heps,Hε⟩:=root_lex_epsilon C N kM (incomingCovector Ω p)
  refine ⟨ε,heps,?_⟩
  intro δ hdδ hδε
  rw [real_perturbed_covector Ω e B hcomp]
  constructor
  · constructor
    · change k (e p)+δ*(Ω p p:ℝ)=0
      have hpp : (Ω p p:ℝ)=0:=by rw [←hcomp,hB]
      rw [hpp,linear_zero_on_plane k r s (e p) hkr hks hpP,mul_zero,add_zero]
    · intro n hn hnN m hm hm0
      have Hs:=Hε δ hdδ hδε n hnN m hm
      have hz : kM m=0:=by
        rcases lt_trichotomy (kM m) 0 with hh|hh|hh
        · exact False.elim (ne_of_lt (Hs.2.1 hh) hm0)
        · exact hh
        · exact False.elim (ne_of_gt (Hs.1 hh) hm0)
      have hmp : B (e m) (e p)=0:=by
        rw [hcomp]
        change kM m+δ*(Ω m p:ℝ)=0 at hm0
        rw [hz,zero_add] at hm0
        exact (mul_eq_zero.mp hm0).resolve_left (ne_of_gt hdδ)
      exact positive_ray_of_pairing_zero e he B hB L r s C hdeg hrs m p n d hn hd hm hp
        (hzero n hnN m hm hz) hpP hmp
  · exact chart_zero_refinement v Ω C kM (incomingCovector Ω p) _ F N (Hε δ hdδ hδε)
lemma joint_roots_plane (N : ℕ) (r : M) (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) (B.flip (e r)) k)
    (a : ℝ) (s : E) (hs : s∈realRootsThrough e C N) (hv : B s (e r)≠0)
    (hsa : (k+a • B.flip (e r)) s=0) :
    ∀n,n ≤ N → ∀m,HasRootDegree C n m → (k+a • B.flip (e r)) (e m)=0 →
      e m∈Submodule.span ℝ {e r,s} := by
  intro n hn m hm hm0
  exact H.joint_plane hs (realRoot_mem e C N n hn m hm) hv a hsa hm0
omit [Algebra ℚ R] in
lemma joint_cut_supported (N : ℕ) (r : M) (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) (B.flip (e r)) k)
    (a : ℝ) (s : E) (hs : s∈realRootsThrough e C N) (hv : B s (e r)≠0)
    (hsa : (k+a • B.flip (e r)) s=0) (F : CompletedPositive v Ω C) :
    ∀n,coeff n (completedCut v Ω C N
      (chartZero v Ω C ((k+a • B.flip (e r)).toAddMonoidHom.comp e) F)).val∈
      supportedSubring v Ω (planeRoots e (e r) s) := by
  apply completedCut_supported v Ω C N _ _
  intro n hn m hm
  by_contra hx
  have hroot:=chart_root_of_ne v Ω C _ n m hx
  have hz : (k+a • B.flip (e r)) (e m)=0:=by
    have Hker:=chartZero_supported_kernel v Ω C ((k+a • B.flip (e r)).toAddMonoidHom.comp e) F n
    by_contra hh
    exact hx (Hker m hh)
  exact hm (joint_roots_plane C e B N r k H a s hs hv hsa n hn m hroot hz)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry RootTruncation WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (e : M →+ E)
def WallsPositiveThrough (N : ℕ) (F : CompletedPositive LaurentRay.vUnit Ω C) : Prop :=
  ∀r d,0 < d → HasRootDegree C d r → ∀h : Module.Dual ℝ E,
    RayGeneric C N r (h.toAddMonoidHom.comp e) →
      RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) F).val
variable (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hcomp in
lemma line_plus_covector (k : Module.Dual ℝ E) (r : M) (a δ : ℝ) :
    (k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e=
      (k+a • B.flip (e r)).toAddMonoidHom.comp e+δ • incomingCovector Ω r := by
  ext m
  change k (e m)+(a+δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ*(Ω m r:ℝ)
  rw [hcomp]; ring
include hcomp in
lemma line_minus_covector (k : Module.Dual ℝ E) (r : M) (a δ : ℝ) :
    (k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e=
      (k+a • B.flip (e r)).toAddMonoidHom.comp e+δ • (-incomingCovector Ω r) := by
  ext m
  change k (e m)+(a-δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ* -(Ω m r:ℝ)
  rw [hcomp]; ring
include he hB hcomp hdeg in
theorem wall_joint_induction (n dr : ℕ) (r : M) (hdr : 0 < dr) (hrd : HasRootDegree C dr r)
    (F : CompletedPositive LaurentRay.vUnit Ω C) (ih : WallsPositiveThrough Ω C e n F)
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C (n+1)) (e r) (B.flip (e r)) k)
    (a : ℝ) (ha : a∈lineEvents (realRootsThrough e C (n+1)) (B.flip (e r)) k) :
    ∃ε > 0,∀δ : ℝ,0 < δ → δ < ε →
      RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C ((k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e) F).val →
      RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C ((k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e) F).val := by
  obtain ⟨s,hs,hsv,hsa⟩:=(mem_lineEvents_iff _ _ _ _).mp ha
  have hrs : B (e r) s≠0:=by
    rw [PlanarRayOrder.alternating_swap B hB]
    exact neg_ne_zero.mpr hsv
  let ka:=k+a • B.flip (e r)
  let kaM:=ka.toAddMonoidHom.comp e
  let J:=chartZero LaurentRay.vUnit Ω C kaM F
  let Jc:=completedCut LaurentRay.vUnit Ω C (n+1) J
  have hkr : ka (e r)=0:=by
    change k (e r)+a*B (e r) (e r)=0
    rw [H.on_ray,hB,mul_zero,add_zero]
  have hks : ka s=0:=hsa
  have hzero:=joint_roots_plane C e B (n+1) r k H a s hs hsv hsa
  have hJc : ∀i,coeff i Jc.val∈supportedSubring LaurentRay.vUnit Ω (planeRoots e (e r) s):=
    joint_cut_supported LaurentRay.vUnit Ω C e B (n+1) r k H a s hs hsv hsa F
  have hcut (h : M →+ ℝ) : ∀i ≤ n+1,
      coeff i (chartZero LaurentRay.vUnit Ω C h Jc).val=coeff i (chartZero LaurentRay.vUnit Ω C h J).val:=by
    apply chartZero_congr_through LaurentRay.vUnit Ω C h Jc J (n+1)
    intro i hi
    exact coeff_cut_of_le J.val hi
  obtain ⟨εp,hεp,Hεp⟩:=root_lex_epsilon C (n+1) kaM (incomingCovector Ω r)
  obtain ⟨εm,hεm,Hεm⟩:=root_lex_epsilon C (n+1) kaM (-incomingCovector Ω r)
  refine ⟨min εp εm,lt_min hεp hεm,?_⟩
  intro δ hδ hδε hright
  have hδp:=lt_of_lt_of_le hδε (min_le_left _ _)
  have hδm:=lt_of_lt_of_le hδε (min_le_right _ _)
  have hrefp:=chart_zero_refinement LaurentRay.vUnit Ω C kaM (incomingCovector Ω r)
    (kaM+δ • incomingCovector Ω r) F (n+1) (Hεp δ hδ hδp)
  have hrefm:=chart_zero_refinement LaurentRay.vUnit Ω C kaM (-incomingCovector Ω r)
    (kaM+δ • (-incomingCovector Ω r)) F (n+1) (Hεm δ hδ hδm)
  have hrpos : RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
      (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω r) Jc).val:=by
    apply hright.congr LaurentRay.vUnit Ω
    intro i hi
    rw [line_plus_covector Ω e B hcomp]
    exact (hrefp i hi).trans (hcut _ i hi).symm
  have hout:=positive_joint_transport Ω C e he B hB hcomp L hdeg n dr r s hdr hrd hrs Jc hJc (by
    intro p d hd hdN hp hpP
    by_cases hpr : Ω p r=0
    · rw [ite_eq_left hpr]
      have hpp : OnPositiveRay r p:=positive_ray_of_pairing_zero e he B hB L (e r) s C hdeg hrs
        p r d dr hd hdr hp hrd hpP (Submodule.subset_span (by simp)) (by rw [hcomp,hpr,Int.cast_zero])
      rw [←hpp.eq_pred,←incoming_same_ray LaurentRay.vUnit Ω C hpp Jc]
      exact hrpos
    · rw [ite_eq_right hpr]
      obtain ⟨η,hη,Hη⟩:=planar_refinement_generic LaurentRay.vUnit Ω C e he B hB hcomp L hdeg
        (n+1) (e r) s hrs ka hkr hks hzero p d hd hp hpP F
      have hη2 : 0 < η/2:=by positivity
      have hηlt : η/2 < η:=by linarith
      obtain ⟨hgen,Href⟩:=Hη (η/2) hη2 hηlt
      have HI:=ih p d hd hp (ka+(η/2) • B.flip (e p)) (hgen.mono C (by omega))
      apply HI.congr LaurentRay.vUnit Ω
      intro i hi
      exact (Href i (by omega)).trans (hcut _ i (by omega)).symm)
  apply hout.congr LaurentRay.vUnit Ω
  intro i hi
  rw [line_minus_covector Ω e B hcomp]
  exact (hcut _ i hi).trans (hrefm i hi).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
