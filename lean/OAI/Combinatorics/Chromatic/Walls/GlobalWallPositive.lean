import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PlanarRefinement
import OAI.Combinatorics.Chromatic.Walls.WallLineInitial

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry FiniteEventTraversal WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

def PositiveIncomingPrescription (F : CompletedPositive LaurentRay.vUnit Ω C) : Prop :=
  ∀r d,0 < d → HasRootDegree C d r → ∃D : CompletedPositive LaurentRay.vUnit Ω C,
    (∀n m,coeff (n+1) D.val m≠0 → OnPositiveRay r m) ∧
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C (OnPositiveRay r)) D.val ∧
    ∀n m,OnPositiveRay r m →
      coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m) F).val) m=
        coeff n (FormalLog.log D.val) m
lemma literalRootProducts_one (P : M → Prop) :
    (1 : PowerSeries (Torus LaurentRay.vUnit Ω))∈literalRootProducts Ω C P :=
  ⟨[],by simp,by simp⟩
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

theorem positive_walls_through (F : CompletedPositive LaurentRay.vUnit Ω C)
    (incoming : PositiveIncomingPrescription Ω C F) : ∀N,WallsPositiveThrough Ω C e N F := by
  intro N
  induction N with
  | zero =>
    intro r d hd hr h hg
    have H:=rootClosedThrough_self LaurentRay.vUnit Ω (N:=0) (literalRootProducts_one Ω C (OnPositiveRay r))
    apply H.congr LaurentRay.vUnit Ω
    intro i hi
    have hi0 : i=0:=by omega
    subst i
    rw [coeff_zero_eq_constantCoeff,map_one,(chartZero LaurentRay.vUnit Ω C _ F).property.1]
  | succ n ih =>
    intro r d hd hr h hg
    let S:=realRootsThrough e C (n+1)
    let vR:=B.flip (e r)
    obtain ⟨k,Hk,Hsign⟩:=exists_generic_offset S (e r) vR h hg.1
    let events:=lineEvents S vR k
    let P (a : ℝ):=RootClosedThrough LaurentRay.vUnit Ω (n+1)
      (literalRootProducts Ω C (OnPositiveRay r))
      (chartZero LaurentRay.vUnit Ω C ((k+a • vR).toAddMonoidHom.comp e) F).val
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
    have hstart : ∃b,0 ≤ b ∧ (∀a∈events,a < b) ∧ P b:=by
      obtain ⟨D,hD,hpos,hpres⟩:=incoming r d hd hr
      obtain ⟨b,hb,hbound,hwall⟩:=incoming_positive_at_far Ω C e he B hB hcomp L hdeg
        (n+1) d r hd hr k Hk F D hD (hpos.cut LaurentRay.vUnit Ω (n+1))
        (fun j hj m hm => hpres j m hm)
      exact ⟨b,hb.le,hbound,hwall⟩
    have hcell : ∀a b,0 ≤ a → 0 ≤ b → a∉events → b∉events →
        (∀z∈events,a < z ↔ b < z) → P a → P b:=by
      intro a b ha hb haS hbS Hside hpa
      apply hpa.congr LaurentRay.vUnit Ω
      apply chart_sign_congr_through LaurentRay.vUnit Ω C _ _ F (n+1)
      intro j hj hjN m hm
      exact line_cell_signs S vR k a b haS hbS Hside (e m) (realRoot_mem e C (n+1) j hjN m hm)
    have hstep : ∀a∈events,0 < a → ∃ε > 0,∀δ : ℝ,0 < δ → δ < ε → P (a+δ) → P (a-δ):=by
      intro a ha ha0
      exact wall_joint_induction Ω C e he B hB hcomp L hdeg n d r hd hr F ih k Hk a ha
    have HK : RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C (k.toAddMonoidHom.comp e) F).val:=by
      have HH:=descend events P hstart hcell hstep 0 (le_refl 0) h0
      simpa only [P,zero_smul,add_zero] using HH
    have Hchart:=chart_sign_congr_through LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (k.toAddMonoidHom.comp e) F (n+1) (by
        intro j hj hjN m hm
        have HS:=Hsign (e m) (realRoot_mem e C (n+1) j hjN m hm)
        refine ⟨HS.1,?_,HS.2⟩
        intro hh
        exact ((hg.2 j hj hjN m hm hh).eval (k.toAddMonoidHom.comp e)).2.1.mpr Hk.on_ray)
    exact HK.congr LaurentRay.vUnit Ω (fun j hj => (Hchart j hj).symm)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
attribute [local instance] Classical.propDecidable
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

def literalIncomingRay (l : List (WallUnitDatum M)) (r : M) :
    PowerSeries (Torus LaurentRay.vUnit Ω) := by
  classical
  exact ((l.filter (fun u => OnPositiveRay r u.root)).map (WallUnitDatum.value Ω)).prod
lemma literalIncomingRay_mem (l : List (WallUnitDatum M))
    (hl : ∀u∈l,u.Allowed C (fun _=>True)) (r : M) :
    literalIncomingRay Ω l r∈literalRootProducts Ω C (OnPositiveRay r) := by
  classical
  refine ⟨l.filter (fun u => OnPositiveRay r u.root),?_,rfl⟩
  intro u hu
  have H:=List.mem_filter.mp hu
  exact ⟨(hl u H.1).1,(hl u H.1).2.1,by simpa using H.2⟩
lemma literalIncomingRay_eq (l : List (WallUnitDatum M)) {r m : M}
    (hm : OnPositiveRay r m) : literalIncomingRay Ω l r=literalIncomingRay Ω l m := by
  classical
  unfold literalIncomingRay
  rw [hm.eq_pred]
def literalIncomingCompleted (l : List (WallUnitDatum M))
    (hl : ∀u∈l,u.Allowed C (fun _=>True)) (r : M) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨literalIncomingRay Ω l r,
    literalRootProducts_constant Ω C _ (literalIncomingRay_mem Ω C l hl r),
    literalRootProducts_graded Ω C _ (literalIncomingRay_mem Ω C l hl r)⟩

def literalIncomingLog (l : List (WallUnitDatum M)) (n : ℕ) : Torus LaurentRay.vUnit Ω := by
  classical
  exact Finsupp.onFinset (rootDegree_finite C n).toFinset
    (fun m => if HasRootDegree C n m then coeff n (FormalLog.log (literalIncomingRay Ω l m)) m else 0)
    (by intro m hm; rw [Set.Finite.mem_toFinset]; by_contra hn; exact hm (ite_eq_right hn))
lemma literalIncomingLog_apply (l : List (WallUnitDatum M)) (n : ℕ) (m : M) :
    literalIncomingLog Ω C l n m=
      if HasRootDegree C n m then coeff n (FormalLog.log (literalIncomingRay Ω l m)) m else 0 := by
  classical
  rfl
lemma literalIncomingLog_graded (l : List (WallUnitDatum M)) (n : ℕ) :
    literalIncomingLog Ω C l n∈rootGrade LaurentRay.vUnit Ω C n := by
  classical
  intro m hm
  rw [literalIncomingLog_apply,ite_eq_right hm]

def literalTotalTransport (l : List (WallUnitDatum M)) : CompletedPositive LaurentRay.vUnit Ω C :=
  ⟨incomingSolution LaurentRay.vUnit Ω C (literalIncomingLog Ω C l),
    incomingSolution_constant LaurentRay.vUnit Ω C _,
    incomingSolution_graded LaurentRay.vUnit Ω C _ (literalIncomingLog_graded Ω C l)⟩
lemma literalTotalTransport_prescription (hΩ : ∀m,Ω m m=0)
    (l : List (WallUnitDatum M)) (hl : ∀u∈l,u.Allowed C (fun _=>True)) :
    PositiveIncomingPrescription Ω C (literalTotalTransport Ω C l) := by
  classical
  intro r d hd hr
  let D:=literalIncomingCompleted Ω C l hl r
  refine ⟨D,?_,inPrecisionClosure_self LaurentRay.vUnit Ω (literalIncomingRay_mem Ω C l hl r),?_⟩
  · intro n m hm
    by_contra hh
    exact hm (literalRootProducts_strictSupport Ω C (OnPositiveRay r)
      (fun a b ha hb=>ha.add hb) (literalIncomingRay_mem Ω C l hl r) n m hh)
  · intro n m hm
    cases n with
    | zero => simp only [coeff_zero_eq_constantCoeff,FormalLog.log_constant,Finsupp.zero_apply]
    | succ n =>
      by_cases hroot : HasRootDegree C (n+1) m
      · have H:=congrArg (fun x : Torus LaurentRay.vUnit Ω=>x m)
          (incomingSolution_prescription LaurentRay.vUnit Ω C hΩ _ (literalIncomingLog_graded Ω C l) n)
        rw [incomingCoefficient_apply,ite_eq_left hroot,literalIncomingLog_apply,ite_eq_left hroot] at H
        change coeff (n+1) (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m)
          (literalTotalTransport Ω C l)).val) m=coeff (n+1) (FormalLog.log (literalIncomingRay Ω l r)) m
        rw [literalIncomingRay_eq Ω l hm]
        exact H
      · rw [root_graded_log LaurentRay.vUnit Ω C _ (n+1) m hroot,
          root_graded_log LaurentRay.vUnit Ω C D (n+1) m hroot]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
