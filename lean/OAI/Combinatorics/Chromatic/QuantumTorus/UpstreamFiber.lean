import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WallLineInitial
import OAI.Combinatorics.Chromatic.Walls.OffCutJoint

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation FiniteRayGeometry FiniteEventTraversal
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hB hcomp hdeg in
lemma upstream_fiber_induction (N : ℕ) (hN : 0<N) (n : ℤ) (P : AddSubmonoid M)
    (pos : Bool) (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (F D : CompletedPositive v Ω C)
    (hD : ∀j m,coeff (j+1) D.val m≠0 → OnPositiveRay r m)
    (hpres : ∀j≤N,∀m,OnPositiveRay r m →
      coeff j (FormalLog.log (chartZero v Ω C (incomingCovector Ω m) F).val) m=
        coeff j (FormalLog.log D.val) m)
    (hDP : ∀j≤N,∀m,coeff j D.val m≠0 → nonpDegree coord pc m=n → m∈P)
    (HI : ∀q d,0<d → HasRootDegree C d q → ∀h : Module.Dual ℝ E,
      RayGeneric C N q (h.toAddMonoidHom.comp e) →
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero v Ω C (h.toAddMonoidHom.comp e) F).val m≠0 →
        nonpDegree coord pc m<n → m∈P)
    (h : Module.Dual ℝ E) (hg : RayGeneric C N r (h.toAddMonoidHom.comp e))
    (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc))
    (htrend : if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0) :
    ∀j≤N,∀m,coeff j (chartZero v Ω C (h.toAddMonoidHom.comp e) F).val m≠0 →
      nonpDegree coord pc m=n → m∈P := by
  classical
  let S:=realRootsThrough e C N
  let vR:=B.flip (e r)
  obtain ⟨k,Hk,Hsign⟩:=exists_generic_offset S (e r) vR h hg.1
  let events:=lineEvents S vR k
  let Q (a : ℝ):=∀j≤N,∀m,
    coeff j (chartZero v Ω C ((k+a • vR).toAddMonoidHom.comp e) F).val m≠0 →
      nonpDegree coord pc m=n → m∈P
  have hsidek : cutSide pos (k.toAddMonoidHom.comp e) (simpleRoot C pc):=by
    have HH:=Hsign (e (simpleRoot C pc)) (realRoot_mem e C N 1 hN _ (simpleRoot_degree C pc))
    cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hside ⊢
    · exact HH.2 hside
    · exact HH.1 hside
  have hsidea (a : ℝ) (ha : 0≤a) :
      cutSide pos ((k+a • vR).toAddMonoidHom.comp e) (simpleRoot C pc):=by
    have heval : ((k+a • vR).toAddMonoidHom.comp e) (simpleRoot C pc)=
        k (e (simpleRoot C pc))+a*(Ω (simpleRoot C pc) r:ℝ):=by
      change k (e (simpleRoot C pc))+a*B (e (simpleRoot C pc)) (e r)=_
      rw [hcomp]
    cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hsidek htrend ⊢ <;> rw [heval]
    · have ht : (Ω (simpleRoot C pc) r:ℝ)≤0:=by exact_mod_cast htrend
      have hk : k (e (simpleRoot C pc))<0:=hsidek
      nlinarith
    · have ht : 0≤(Ω (simpleRoot C pc) r:ℝ):=by exact_mod_cast htrend
      have hk : 0<k (e (simpleRoot C pc)):=hsidek
      nlinarith
  have h0 : (0:ℝ)∉events:=by
    intro hevent
    obtain ⟨s,hs,hv,hs0⟩:=(mem_lineEvents_iff S vR k 0).mp hevent
    have hn : s∉Submodule.span ℝ {e r}:=by
      intro hmem
      obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp hmem
      apply hv
      rw [←hc,map_smul]
      change c*B (e r) (e r)=0
      rw [hB,mul_zero]
    apply Hk.avoid s hs hn
    simpa only [zero_smul,add_zero] using hs0
  have hstart : ∃b,0≤b ∧ (∀a∈events,a<b) ∧ Q b:=by
    obtain ⟨b,hb,hbound⟩:=finite_upper_bound events
    have hΩ : ∀m,Ω m m=0:=by
      intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
    have Hgen:=offset_ray_generic C e he L hdeg N dr r hdr hrd vR k Hk
    have Hinc:=incoming_ray_element_through v Ω C hΩ r (k.toAddMonoidHom.comp e)
      Hk.on_ray F D N (fun j hj hjN m hm hΩm hkm=>Hgen.2 j hj hjN m hm hkm) hD hpres
    have Href:=chart_zero_refinement v Ω C (incomingCovector Ω r) (k.toAddMonoidHom.comp e)
      ((k+b • vR).toAddMonoidHom.comp e) F N (by
        intro j hj m hm
        have HH:=far_line_lex S vR k b hbound (e m) (realRoot_mem e C N j hj m hm)
        simp only [vR,LinearMap.flip_apply,hcomp] at HH
        exact HH)
    refine ⟨b,hb.le,hbound,?_⟩
    intro j hj m hm hn
    apply hDP j hj m ?_ hn
    rw [Href j hj,Hinc j hj] at hm
    exact hm
  have hcell : ∀a b,0≤a → 0≤b → a∉events → b∉events →
      (∀z∈events,a<z ↔ b<z) → Q a → Q b:=by
    intro a b ha hb haS hbS Hside hpa
    have Hchart:=chart_sign_congr_through v Ω C
      ((k+a • vR).toAddMonoidHom.comp e) ((k+b • vR).toAddMonoidHom.comp e) F N (by
        intro j hj hjN m hm
        exact line_cell_signs S vR k a b haS hbS Hside (e m) (realRoot_mem e C N j hjN m hm))
    intro j hj m hm hn
    apply hpa j hj m ?_ hn
    rwa [Hchart j hj]
  have hstep : ∀a∈events,0<a → ∃ε>0,∀δ : ℝ,0<δ → δ<ε → Q (a+δ) → Q (a-δ):=by
    intro a ha ha0
    obtain ⟨s,hs,hsv,hsa⟩:=(mem_lineEvents_iff S vR k a).mp ha
    have hrs : B (e r) s≠0:=by
      rw [PlanarRayOrder.alternating_swap B hB]
      exact neg_ne_zero.mpr hsv
    let ka:=k+a • vR
    let kaM:=ka.toAddMonoidHom.comp e
    have hkr : ka (e r)=0:=by
      change k (e r)+a*B (e r) (e r)=0
      rw [Hk.on_ray,hB,mul_zero,add_zero]
    have hzero:=joint_roots_plane C e B N r k Hk a s hs hsv hsa
    obtain ⟨εp,hεp,Hεp⟩:=root_lex_epsilon C N kaM (incomingCovector Ω r)
    obtain ⟨εm,hεm,Hεm⟩:=root_lex_epsilon C N kaM (-incomingCovector Ω r)
    refine ⟨min εp εm,lt_min hεp hεm,?_⟩
    intro δ hδ hδε hright
    have hrefp:=chart_zero_refinement v Ω C kaM (incomingCovector Ω r)
      (kaM+δ • incomingCovector Ω r) F N (Hεp δ hδ (lt_of_lt_of_le hδε (min_le_left _ _)))
    have hrefm:=chart_zero_refinement v Ω C kaM (-incomingCovector Ω r)
      (kaM+δ • (-incomingCovector Ω r)) F N (Hεm δ hδ (lt_of_lt_of_le hδε (min_le_right _ _)))
    have hlp : ((k+(a+δ) • vR).toAddMonoidHom.comp e)=kaM+δ • incomingCovector Ω r:=by
      ext m; change k (e m)+(a+δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ*(Ω m r:ℝ)
      rw [hcomp]; ring
    have hlm : ((k+(a-δ) • vR).toAddMonoidHom.comp e)=kaM+δ • (-incomingCovector Ω r):=by
      ext m; change k (e m)+(a-δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ* -(Ω m r:ℝ)
      rw [hcomp]; ring
    have HH:=offcut_planar_support v Ω C coord hcoord pc e he B hB hcomp L hdeg N hN n P pos r dr hdr hrd
      s hrs ka hkr hsa hzero (hsidea a ha0.le) F HI (by
        intro j hj m hm hn
        apply hright j hj m ?_ hn
        rw [hlp,hrefp j hj]
        exact hm)
    intro j hj m hm hn
    rw [hlm,hrefm j hj] at hm
    exact HH j hj m hm hn
  have HK : ∀j≤N,∀m,coeff j (chartZero v Ω C (k.toAddMonoidHom.comp e) F).val m≠0 →
      nonpDegree coord pc m=n → m∈P:=by
    have HH:=descend events Q hstart hcell hstep 0 (le_refl 0) h0
    simpa only [Q,zero_smul,add_zero] using HH
  have Hchart:=chart_sign_congr_through v Ω C (h.toAddMonoidHom.comp e) (k.toAddMonoidHom.comp e) F N (by
    intro j hj hjN m hm
    have HS:=Hsign (e m) (realRoot_mem e C N j hjN m hm)
    refine ⟨HS.1,?_,HS.2⟩
    intro hh
    exact ((hg.2 j hj hjN m hm hh).eval (k.toAddMonoidHom.comp e)).2.1.mpr Hk.on_ray)
  intro j hj m hm hn
  apply HK j hj m ?_ hn
  rwa [←Hchart j hj]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
