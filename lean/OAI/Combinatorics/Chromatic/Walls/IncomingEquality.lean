import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationRootMap

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma literalTotalTransport_log_ray (hΩ : ∀m,Ω m m=0)
    (l : List (WallUnitDatum M)) (hl : ∀u∈l,u.Allowed C (fun _=>True))
    (r : M) (n : ℕ) (m : M) (hm : OnPositiveRay r m) :
    coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m)
      (literalTotalTransport Ω C l)).val) m=
    coeff n (FormalLog.log (literalIncomingRay Ω l r)) m := by
  classical
  cases n with
  | zero => simp only [coeff_zero_eq_constantCoeff,FormalLog.log_constant,Finsupp.zero_apply]
  | succ n =>
    by_cases hroot : HasRootDegree C (n+1) m
    · have H:=congrArg (fun x : Torus LaurentRay.vUnit Ω=>x m)
        (incomingSolution_prescription LaurentRay.vUnit Ω C hΩ _ (literalIncomingLog_graded Ω C l) n)
      rw [incomingCoefficient_apply,ite_eq_left hroot,literalIncomingLog_apply,ite_eq_left hroot] at H
      rw [literalIncomingRay_eq Ω l hm]
      exact H
    · exact (root_graded_log LaurentRay.vUnit Ω C _ (n+1) m hroot).trans
        (root_graded_log LaurentRay.vUnit Ω C (literalIncomingCompleted Ω C l hl r)
          (n+1) m hroot).symm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
lemma literal_incoming_at_far_through
    (l : List (WallUnitDatum M)) (hl : ∀u∈l,u.Allowed C (fun _=>True))
    (N d : ℕ) (r : M) (hd : 0<d) (hr : HasRootDegree C d r)
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) (B.flip (e r)) k)
    (b : ℝ) (hb : ∀a∈lineEvents (realRootsThrough e C N) (B.flip (e r)) k,a<b) :
    ∀n≤N,coeff n (chartZero LaurentRay.vUnit Ω C
      ((k+b • B.flip (e r)).toAddMonoidHom.comp e) (literalTotalTransport Ω C l)).val=
      coeff n (literalIncomingRay Ω l r) := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  let D:=literalIncomingCompleted Ω C l hl r
  have Hgen:=offset_ray_generic C e he L hdeg N d r hd hr (B.flip (e r)) k H
  have Hinc:=incoming_ray_element_through LaurentRay.vUnit Ω C hΩ r (k.toAddMonoidHom.comp e)
    H.on_ray (literalTotalTransport Ω C l) D N
    (fun n hn hnN m hm hΩm hkm=>Hgen.2 n hn hnN m hm hkm)
    (by
      intro n m hm
      by_contra hh
      exact hm (literalRootProducts_strictSupport Ω C (OnPositiveRay r)
        (fun a b ha hb=>ha.add hb) (literalIncomingRay_mem Ω C l hl r) n m hh))
    (by intro n hn m hm; exact literalTotalTransport_log_ray Ω C hΩ l hl r n m hm)
  have Href:=chart_zero_refinement LaurentRay.vUnit Ω C (incomingCovector Ω r)
    (k.toAddMonoidHom.comp e) ((k+b • B.flip (e r)).toAddMonoidHom.comp e)
    (literalTotalTransport Ω C l) N (by
      intro n hn m hm
      have HH:=far_line_lex (realRootsThrough e C N) (B.flip (e r)) k b hb
        (e m) (realRoot_mem e C N n hn m hm)
      simp only [LinearMap.flip_apply,hcomp] at HH
      exact HH)
  intro n hn
  exact (Href n hn).trans (Hinc n hn)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (p : M) (hp : Ω p p=0)

def shearCovector (h : M →+ ℝ) : M →+ ℝ := h.comp (mutationShearInverse Ω p)
def shearCovectorInverse (h : M →+ ℝ) : M →+ ℝ := h.comp (mutationShear Ω p)
include hp in
lemma shearCovector_at_p (h : M →+ ℝ) : shearCovector Ω p h p=h p := by
  change h (p+Ω p p • p)=h p
  rw [hp,zero_zsmul,add_zero]
include hp in
lemma shearCovectorInverse_at_p (h : M →+ ℝ) : shearCovectorInverse Ω p h p=h p := by
  change h (p-Ω p p • p)=h p
  rw [hp,zero_zsmul,sub_zero]
include hp in
lemma shearCovector_inv (h : M →+ ℝ) :
    shearCovector Ω p (shearCovectorInverse Ω p h)=h := by
  ext m
  exact congrArg h (mutationShear_right_inverse Ω p hp m)
include hp in
lemma shearCovector_inv' (h : M →+ ℝ) :
    shearCovectorInverse Ω p (shearCovector Ω p h)=h := by
  ext m
  exact congrArg h (mutationShear_left_inverse Ω p hp m)
lemma shearCovector_on_cut (h : M →+ ℝ) (hh : h p=0) : shearCovector Ω p h=h := by
  ext m
  change h (m+Ω p m • p)=h m
  rw [map_add,map_zsmul,hh,smul_zero,add_zero]

def mutationCovector (h : M →+ ℝ) : M →+ ℝ :=
  if 0≤h p then h else shearCovector Ω p h
def mutationCovectorInverse (h : M →+ ℝ) : M →+ ℝ :=
  if 0≤h p then h else shearCovectorInverse Ω p h
include hp in
lemma mutationCovector_at_p (h : M →+ ℝ) : mutationCovector Ω p h p=h p := by
  unfold mutationCovector
  split_ifs <;> first | rfl | exact shearCovector_at_p Ω p hp h
include hp in
lemma mutationCovectorInverse_at_p (h : M →+ ℝ) : mutationCovectorInverse Ω p h p=h p := by
  unfold mutationCovectorInverse
  split_ifs <;> first | rfl | exact shearCovectorInverse_at_p Ω p hp h
include hp in
lemma mutationCovector_left_inverse (h : M →+ ℝ) :
    mutationCovectorInverse Ω p (mutationCovector Ω p h)=h := by
  unfold mutationCovectorInverse
  rw [mutationCovector_at_p Ω p hp]
  unfold mutationCovector
  split_ifs <;> first | rfl | exact shearCovector_inv' Ω p hp h
include hp in
lemma mutationCovector_right_inverse (h : M →+ ℝ) :
    mutationCovector Ω p (mutationCovectorInverse Ω p h)=h := by
  unfold mutationCovector
  rw [mutationCovectorInverse_at_p Ω p hp]
  unfold mutationCovectorInverse
  split_ifs <;> first | rfl | exact shearCovector_inv Ω p hp h

def mutationCovectorEquiv : (M →+ ℝ) ≃ (M →+ ℝ) where
  toFun:=mutationCovector Ω p
  invFun:=mutationCovectorInverse Ω p
  left_inv:=mutationCovector_left_inverse Ω p hp
  right_inv:=mutationCovector_right_inverse Ω p hp

lemma incoming_shear_covariance (hΩ : ∀m,Ω m m=0) (r : M) :
    incomingCovector Ω (mutationShear Ω p r)=shearCovector Ω p (incomingCovector Ω r) := by
  ext m
  change (Ω m (mutationShear Ω p r):ℝ)=(Ω (mutationShearInverse Ω p m) r:ℝ)
  have H:=mutationShear_pairing Ω hΩ p (mutationShearInverse Ω p m) r
  rw [mutationShear_right_inverse Ω p (hΩ p)] at H
  exact congrArg (fun z : ℤ=>(z:ℝ)) H

def mutationIncomingLabel (m : M) : M := m+max 0 (-Ω p m) • p
def mutationIncomingLabelInverse (m : M) : M := m-max 0 (-Ω p m) • p
include hp in
lemma mutationIncomingLabel_pairing (m : M) : Ω p (mutationIncomingLabel Ω p m)=Ω p m := by
  change Ω p (m+max 0 (-Ω p m) • p)=Ω p m
  rw [map_add,map_zsmul,hp,smul_zero,add_zero]
include hp in
lemma mutationIncomingLabelInverse_pairing (m : M) : Ω p (mutationIncomingLabelInverse Ω p m)=Ω p m := by
  change Ω p (m-max 0 (-Ω p m) • p)=Ω p m
  rw [map_sub,map_zsmul,hp,smul_zero,sub_zero]
include hp in
lemma mutationIncomingLabel_left_inverse (m : M) :
    mutationIncomingLabelInverse Ω p (mutationIncomingLabel Ω p m)=m := by
  unfold mutationIncomingLabelInverse
  rw [mutationIncomingLabel_pairing Ω p hp]
  exact add_sub_cancel_right m _
include hp in
lemma mutationIncomingLabel_right_inverse (m : M) :
    mutationIncomingLabel Ω p (mutationIncomingLabelInverse Ω p m)=m := by
  unfold mutationIncomingLabel
  rw [mutationIncomingLabelInverse_pairing Ω p hp]
  exact sub_add_cancel m _
def mutationIncomingLabelEquiv : M ≃ M where
  toFun:=mutationIncomingLabel Ω p
  invFun:=mutationIncomingLabelInverse Ω p
  left_inv:=mutationIncomingLabel_left_inverse Ω p hp
  right_inv:=mutationIncomingLabel_right_inverse Ω p hp
lemma mutationIncomingLabel_nonnegative (m : M) (hm : 0≤Ω p m) : mutationIncomingLabel Ω p m=m := by
  rw [mutationIncomingLabel,max_eq_left (by omega),zero_zsmul,add_zero]
lemma mutationIncomingLabel_nonpositive (m : M) (hm : Ω p m≤0) :
    mutationIncomingLabel Ω p m=mutationShear Ω p m := by
  rw [mutationIncomingLabel,max_eq_right (by omega),neg_zsmul]
  exact (sub_eq_add_neg _ _).symm
lemma incoming_mutation_covariance (hΩ : ∀m,Ω m m=0) (r : M) :
    incomingCovector Ω (mutationIncomingLabel Ω p r)=mutationCovector Ω p (incomingCovector Ω r) := by
  by_cases hr : 0≤Ω p r
  · rw [mutationIncomingLabel_nonnegative Ω p r hr,mutationCovector,ite_eq_left]
    change (0:ℝ)≤(Ω p r:ℝ)
    exact_mod_cast hr
  · have hr' : Ω p r≤0:=le_of_lt (lt_of_not_ge hr)
    rw [mutationIncomingLabel_nonpositive Ω p r hr',incoming_shear_covariance Ω p hΩ r,
      mutationCovector,ite_eq_right]
    change ¬(0:ℝ)≤(Ω p r:ℝ)
    exact_mod_cast hr
end
end ElementaryPositivity.QuantumTorus

end

end OAI
