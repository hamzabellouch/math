import Mathlib
import OAI.Combinatorics.Chromatic.Walls.IncomingEquality

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
variable (Ω : M →+ M →+ ℤ) (e : M →+ E)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M)
variable (hS : ∀x,S x x=0) (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))

def realShearCovector (h : Module.Dual ℝ E) : Module.Dual ℝ E := h+(h (e p)) • S (e p)
def realShearCovectorInverse (h : Module.Dual ℝ E) : Module.Dual ℝ E := h-(h (e p)) • S (e p)
include hS in
lemma realShearCovector_at_p (h : Module.Dual ℝ E) :
    realShearCovector e S p h (e p)=h (e p) := by
  simp [realShearCovector,hS]
include hS in
lemma realShearCovectorInverse_at_p (h : Module.Dual ℝ E) :
    realShearCovectorInverse e S p h (e p)=h (e p) := by
  simp [realShearCovectorInverse,hS]
include hS in
lemma realShearCovector_left_inverse (h : Module.Dual ℝ E) :
    realShearCovectorInverse e S p (realShearCovector e S p h)=h := by
  rw [realShearCovectorInverse,realShearCovector_at_p e S p hS]
  exact add_sub_cancel_right h _
include hS in
lemma realShearCovector_right_inverse (h : Module.Dual ℝ E) :
    realShearCovector e S p (realShearCovectorInverse e S p h)=h := by
  rw [realShearCovector,realShearCovectorInverse_at_p e S p hS]
  exact sub_add_cancel h _

def realMutationCovector (h : Module.Dual ℝ E) : Module.Dual ℝ E :=
  if 0≤h (e p) then h else realShearCovector e S p h
def realMutationCovectorInverse (h : Module.Dual ℝ E) : Module.Dual ℝ E :=
  if 0≤h (e p) then h else realShearCovectorInverse e S p h
include hS in
lemma realMutationCovector_at_p (h : Module.Dual ℝ E) :
    realMutationCovector e S p h (e p)=h (e p) := by
  unfold realMutationCovector
  split_ifs <;> first | rfl | exact realShearCovector_at_p e S p hS h
include hS in
lemma realMutationCovectorInverse_at_p (h : Module.Dual ℝ E) :
    realMutationCovectorInverse e S p h (e p)=h (e p) := by
  unfold realMutationCovectorInverse
  split_ifs <;> first | rfl | exact realShearCovectorInverse_at_p e S p hS h
include hS in
lemma realMutationCovector_left_inverse (h : Module.Dual ℝ E) :
    realMutationCovectorInverse e S p (realMutationCovector e S p h)=h := by
  unfold realMutationCovectorInverse
  rw [realMutationCovector_at_p e S p hS]
  unfold realMutationCovector
  split_ifs <;> first | rfl | exact realShearCovector_left_inverse e S p hS h
include hS in
lemma realMutationCovector_right_inverse (h : Module.Dual ℝ E) :
    realMutationCovector e S p (realMutationCovectorInverse e S p h)=h := by
  unfold realMutationCovector
  rw [realMutationCovectorInverse_at_p e S p hS]
  unfold realMutationCovectorInverse
  split_ifs <;> first | rfl | exact realShearCovector_right_inverse e S p hS h

def realMutationCovectorEquiv : Module.Dual ℝ E ≃ Module.Dual ℝ E where
  toFun:=realMutationCovector e S p
  invFun:=realMutationCovectorInverse e S p
  left_inv:=realMutationCovector_left_inverse e S p hS
  right_inv:=realMutationCovector_right_inverse e S p hS

include hcomp in
lemma realShearCovector_lattice (h : Module.Dual ℝ E) :
    (realShearCovector e S p h).toAddMonoidHom.comp e=shearCovector Ω p (h.toAddMonoidHom.comp e) := by
  ext m
  change h (e m)+h (e p)*S (e p) (e m)=h (e (m+Ω p m • p))
  rw [hcomp,map_add,map_zsmul,map_add,map_zsmul]
  simp only [zsmul_eq_mul]
  ring
include hcomp in
lemma realMutationCovector_lattice (h : Module.Dual ℝ E) :
    (realMutationCovector e S p h).toAddMonoidHom.comp e=
      mutationCovector Ω p (h.toAddMonoidHom.comp e) := by
  unfold realMutationCovector mutationCovector
  change (if 0≤h (e p) then h else realShearCovector e S p h).toAddMonoidHom.comp e=
    if 0≤h (e p) then h.toAddMonoidHom.comp e else shearCovector Ω p (h.toAddMonoidHom.comp e)
  split_ifs <;> first | rfl | exact realShearCovector_lattice Ω e S p hcomp h

include hS hcomp in
lemma realMutationCovector_incoming (r : M) :
    realMutationCovector e S p (S.flip (e r))=S.flip (e (mutationIncomingLabel Ω p r)) := by
  have hs : ∀a b,S a b= -S b a:=by
    intro a b
    have H:=hS (a+b)
    simp only [map_add,LinearMap.add_apply,hS] at H
    linarith
  ext x
  by_cases hp : (0:ℝ)≤S (e p) (e r)
  · have hp' : 0≤Ω p r:=by rw [hcomp] at hp; exact_mod_cast hp
    have hflip : 0≤(S.flip (e r)) (e p):=hp
    rw [realMutationCovector,ite_eq_left hflip,mutationIncomingLabel_nonnegative Ω p r hp']
  · have hp' : Ω p r≤0:=by
      have hh : S (e p) (e r)≤0:=le_of_lt (lt_of_not_ge hp)
      rw [hcomp] at hh
      exact_mod_cast hh
    have hflip : ¬0≤(S.flip (e r)) (e p):=hp
    rw [realMutationCovector,ite_eq_right hflip,mutationIncomingLabel_nonpositive Ω p r hp']
    change S x (e r)+S (e p) (e r)*S (e p) x=S x (e (r-Ω p r • p))
    rw [map_sub,map_zsmul,map_sub,map_zsmul,hcomp,hs x (e p)]
    simp only [zsmul_eq_mul]
    ring
end
end ElementaryPositivity.QuantumTorus

end

end OAI
