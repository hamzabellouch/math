import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.SimplePlaneGeometry
import OAI.Combinatorics.Chromatic.QuantumTorus.UpstreamFiber

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
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hB hcomp hdeg in
lemma upstream_simple_fiber (N : ℕ) (hN : 0<N) (n : ℤ) (pos : Bool)
    (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (hr : 0<nonpDegree coord pc r)
    (HI : ∀q d,0<d → HasRootDegree C d q → ∀h : Module.Dual ℝ E,
      RayGeneric C N q (h.toAddMonoidHom.comp e) →
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m<n →
        m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (h : Module.Dual ℝ E) (hg : RayGeneric C N r (h.toAddMonoidHom.comp e))
    (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc))
    (htrend : 0≤ sideSign pos*Ω (simpleRoot C pc) r) :
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m=n →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have H:=hB (e m); rw [hcomp] at H; exact_mod_cast H
  apply upstream_fiber_induction LaurentRay.vUnit Ω C coord hcoord pc e he B hB hcomp L hdeg
    N hN n _ pos r dr hdr hrd (simpleTotalTransport Ω C)
    (literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) r)
    (by
      intro j m hm
      by_contra hh
      exact hm (literalRootProducts_strictSupport Ω C (OnPositiveRay r)
        (fun a b ha hb=>ha.add hb) (literalIncomingRay_mem Ω C
          (simpleIncomingList C) (simpleIncomingList_allowed C) r) j m hh))
    (fun j _ m hm=>literalTotalTransport_ray_prescription Ω C hΩ
      (simpleIncomingList C) (simpleIncomingList_allowed C) r j m hm) ?_ HI h hg hside ?_
  · intro j hj m hm hn
    by_contra hh
    exact hm (simpleIncomingCompleted_fiber Ω C coord hcoord pc r hr
      (mutationPairing Ω C pc) (sideSign pos) j m hh)
  · cases pos <;> simpa [sideSign] using htrend
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation FiniteRayGeometry FiniteEventTraversal WallUnits
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
lemma global_simple_fiber_step (N : ℕ) (hN : 0<N) (n : ℤ)
    (HI : ∀q d,0<d → HasRootDegree C d q → ∀h : Module.Dual ℝ E,
      RayGeneric C N q (h.toAddMonoidHom.comp e) → ∀pos : Bool,
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m<n →
        m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m=n →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  classical
  let p:=simpleRoot C pc
  let F:=simpleTotalTransport Ω C
  have hp : (h.toAddMonoidHom.comp e) p≠0:=by
    cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hside
    · exact ne_of_lt hside
    · exact ne_of_gt hside
  have hr : 0<nonpDegree coord pc r:=nonp_positive_off_cut C coord hcoord pc hdr hrd
    (h.toAddMonoidHom.comp e) hp hg.1
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have H:=hB (e m); rw [hcomp] at H; exact_mod_cast H
  have HU (side : Bool) : ∀q d,0<d → HasRootDegree C d q →
      0<sideSign side*Ω p q → ∀b : Module.Dual ℝ E,
      RayGeneric C N q (b.toAddMonoidHom.comp e) → cutSide side (b.toAddMonoidHom.comp e) p →
      ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (b.toAddMonoidHom.comp e) F).val m≠0 →
        nonpDegree coord pc m≤n → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign side):=by
    intro q d hd hdq ht b hb hs j hj m hm hn
    by_cases hn' : nonpDegree coord pc m<n
    · exact HI q d hd hdq b hb side hs j hj m hm hn'
    have hqn : 0<nonpDegree coord pc q:=by
      apply nonp_positive_off_cut C coord hcoord pc hd hdq (b.toAddMonoidHom.comp e) ?_ hb.1
      cases side <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hs
      · exact ne_of_lt hs
      · exact ne_of_gt hs
    exact upstream_simple_fiber Ω C coord hcoord pc e he B hB hcomp L hdeg N hN n side q d hd hdq hqn
      (fun q d hd hr b hb hs=>HI q d hd hr b hb side hs) b hb hs ht.le j hj m hm (by omega)
  let S:=realRootsThrough e C N
  let vR:=B.flip (e r)
  obtain ⟨k,Hk,Hsign⟩:=exists_generic_offset S (e r) vR h hg.1
  let events:=lineEvents S vR k
  let P (side : Bool):=fiberCone coord pc (mutationPairing Ω C pc) (sideSign side)
  let Q (a : ℝ):=∀side : Bool,cutSide side ((k+a • vR).toAddMonoidHom.comp e) p →
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C ((k+a • vR).toAddMonoidHom.comp e) F).val m≠0 →
      nonpDegree coord pc m=n → m∈P side
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
    let D:=literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) r
    have Hgen:=offset_ray_generic C e he L hdeg N dr r hdr hrd vR k Hk
    have Hinc:=incoming_ray_element_through LaurentRay.vUnit Ω C hΩ r (k.toAddMonoidHom.comp e)
      Hk.on_ray F D N (fun j hj hjN m hm hΩm hkm=>Hgen.2 j hj hjN m hm hkm)
      (by intro j m hm; by_contra hh; exact hm (literalRootProducts_strictSupport Ω C (OnPositiveRay r)
        (fun a b ha hb=>ha.add hb) (literalIncomingRay_mem Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) r) j m hh))
      (fun j _ m hm=>literalTotalTransport_ray_prescription Ω C hΩ (simpleIncomingList C)
        (simpleIncomingList_allowed C) r j m hm)
    have Href:=chart_zero_refinement LaurentRay.vUnit Ω C (incomingCovector Ω r) (k.toAddMonoidHom.comp e)
      ((k+b • vR).toAddMonoidHom.comp e) F N (by
        intro j hj m hm
        have HH:=far_line_lex S vR k b hbound (e m) (realRoot_mem e C N j hj m hm)
        simp only [vR,LinearMap.flip_apply,hcomp] at HH
        exact HH)
    refine ⟨b,hb.le,hbound,?_⟩
    intro side hs j hj m hm hn
    by_contra hh
    apply hm
    rw [Href j hj,Hinc j hj]
    exact simpleIncomingCompleted_fiber Ω C coord hcoord pc r hr (mutationPairing Ω C pc) (sideSign side) j m hh
  have hcell : ∀a b,0≤a → 0≤b → a∉events → b∉events →
      (∀z∈events,a<z ↔ b<z) → Q a → Q b:=by
    intro a b ha hb haS hbS Hside Hpa side hs j hj m hm hn
    have Hsigns:=line_cell_signs S vR k a b haS hbS Hside
    have Hchart:=chart_sign_congr_through LaurentRay.vUnit Ω C
      ((k+a • vR).toAddMonoidHom.comp e) ((k+b • vR).toAddMonoidHom.comp e) F N
      (fun j hj hjN m hm=>Hsigns (e m) (realRoot_mem e C N j hjN m hm))
    have hs' : cutSide side ((k+a • vR).toAddMonoidHom.comp e) p:=by
      have HH:=line_cell_signs S vR k b a hbS haS (fun z hz=>(Hside z hz).symm)
        (e p) (realRoot_mem e C N 1 hN p (simpleRoot_degree C pc))
      cases side <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hs ⊢
      · exact HH.2.2 hs
      · exact HH.1 hs
    apply Hpa side hs' j hj m ?_ hn
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
    intro δ hδ hδε hright side hsideδ j hj m hm hn
    have hδp : δ<εp:=lt_of_lt_of_le hδε (min_le_left _ _)
    have hδm : δ<εm:=lt_of_lt_of_le hδε (min_le_right _ _)
    have hrefp:=chart_zero_refinement LaurentRay.vUnit Ω C kaM (incomingCovector Ω r)
      (kaM+δ • incomingCovector Ω r) F N (Hεp δ hδ hδp)
    have hrefm:=chart_zero_refinement LaurentRay.vUnit Ω C kaM (-incomingCovector Ω r)
      (kaM+δ • (-incomingCovector Ω r)) F N (Hεm δ hδ hδm)
    have hlp : ((k+(a+δ) • vR).toAddMonoidHom.comp e)=kaM+δ • incomingCovector Ω r:=by
      ext m; change k (e m)+(a+δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ*(Ω m r:ℝ)
      rw [hcomp]; ring
    have hlm : ((k+(a-δ) • vR).toAddMonoidHom.comp e)=kaM+δ • (-incomingCovector Ω r):=by
      ext m; change k (e m)+(a-δ)*B (e m) (e r)=k (e m)+a*B (e m) (e r)+δ* -(Ω m r:ℝ)
      rw [hcomp]; ring
    rw [hlm,hrefm j hj] at hm
    by_cases hkp : kaM p=0
    · have hpr : Ω p r≠0:=by
        intro hz
        have hkp' : k (e p)=0:=by
          change k (e p)+a*B (e p) (e r)=0 at hkp
          simpa only [hcomp,hz,Int.cast_zero,mul_zero,add_zero] using hkp
        have Hgen:=offset_ray_generic C e he L hdeg N dr r hdr hrd vR k Hk
        exact positive_nonp_not_simple_ray C coord hcoord pc r hr
          (Hgen.2 1 Nat.zero_lt_one hN p (simpleRoot_degree C pc) hkp')
      have hprR : B (e p) (e r)≠0:=by rw [hcomp]; exact_mod_cast hpr
      have hzero' : ∀d,d≤N → ∀m,HasRootDegree C d m → ka (e m)=0 →
          m∈planeRoots e (e p) (e r):=by
        intro d hd m hm hz
        have HG:=joint_roots_plane C e B N r k Hk a (e p)
          (realRoot_mem e C N 1 hN p (simpleRoot_degree C pc)) hprR hkp d hd m hm hz
        change e m∈Submodule.span ℝ {e p,e r}
        simpa only [Set.pair_comm (e r) (e p)] using HG
      have ht : 0<sideSign (!side)*Ω p r:=by
        rw [hlm] at hsideδ
        have hev : (kaM+δ • (-incomingCovector Ω r)) p= -δ*(Ω p r:ℝ):=by
          change kaM p+δ*(-(Ω p r:ℝ))=_
          rw [hkp]; ring
        cases side <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hsideδ <;>
          rw [hev] at hsideδ
        · have HP : 0<(Ω p r:ℝ):=by nlinarith
          simpa [sideSign] using (show 0<Ω p r from by exact_mod_cast HP)
        · have HP : (Ω p r:ℝ)<0:=by nlinarith
          simpa [sideSign] using (show Ω p r<0 from by exact_mod_cast HP)
      have HH:=cut_planar_fiber Ω C coord hcoord pc e he B hB hcomp L hdeg N n (!side)
        r hr ht ka hkp hkr hzero' (HU (!side)) j hj m hm (le_of_eq hn)
      change m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign side)
      simpa only [sideSign_neg,neg_neg] using HH
    · have hsignp:=Hεp δ hδ hδp 1 hN p (simpleRoot_degree C pc)
      have hsignm:=Hεm δ hδ hδm 1 hN p (simpleRoot_degree C pc)
      have hs0 : cutSide side kaM p:=by
        rw [hlm] at hsideδ
        cases side <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hsideδ ⊢
        · by_contra hh
          have hp : 0<kaM p:=lt_of_le_of_ne (by linarith) (Ne.symm hkp)
          have HH:=hsignm.1 hp
          linarith
        · by_contra hh
          have hp : kaM p<0:=lt_of_le_of_ne (by linarith) hkp
          have HH:=hsignm.2.1 hp
          linarith
      have hsplus : cutSide side ((k+(a+δ) • vR).toAddMonoidHom.comp e) p:=by
        rw [hlp]
        cases side <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hs0 ⊢
        · exact hsignp.2.1 hs0
        · exact hsignp.1 hs0
      exact offcut_planar_support LaurentRay.vUnit Ω C coord hcoord pc e he B hB hcomp L hdeg N hN n
        (P side) side r dr hdr hrd s hrs ka hkr hsa hzero hs0 F
        (fun q d hd hr b hb hs=>HI q d hd hr b hb side hs)
        (by
          intro j hj m hm hn
          apply hright side hsplus j hj m ?_ hn
          rw [hlp,hrefp j hj]; exact hm) j hj m hm hn
  have HK : Q 0:=descend events Q hstart hcell hstep 0 (le_refl 0) h0
  have hsidek : cutSide pos (k.toAddMonoidHom.comp e) p:=by
    have HH:=Hsign (e p) (realRoot_mem e C N 1 hN p (simpleRoot_degree C pc))
    cases pos <;> simp only [cutSide,Bool.false_eq_true,ite_false,ite_true] at hside ⊢
    · exact HH.2 hside
    · exact HH.1 hside
  have Hchart:=chart_sign_congr_through LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
    (k.toAddMonoidHom.comp e) F N (by
      intro j hj hjN m hm
      have HS:=Hsign (e m) (realRoot_mem e C N j hjN m hm)
      refine ⟨HS.1,?_,HS.2⟩
      intro hh
      exact ((hg.2 j hj hjN m hm hh).eval (k.toAddMonoidHom.comp e)).2.1.mpr Hk.on_ray)
  intro j hj m hm hn
  have HK':=HK pos (by simpa only [zero_smul,add_zero] using hsidek) j hj m
  apply HK' ?_ hn
  simpa only [zero_smul,add_zero] using (show coeff j (chartZero LaurentRay.vUnit Ω C
    (k.toAddMonoidHom.comp e) F).val m≠0 from by rwa [←Hchart j hj])
end
end ElementaryPositivity.QuantumTorus

end

end OAI
