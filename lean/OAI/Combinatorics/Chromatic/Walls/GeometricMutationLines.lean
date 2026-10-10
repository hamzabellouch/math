import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WallRegrade
import OAI.Combinatorics.Chromatic.QuantumTorus.GeometricMutation

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
variable (Ω : M →+ M →+ ℤ) (e : M →+ E)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M)
variable (hS : ∀x,S x x=0) (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
lemma realShearCovector_add (h k : Module.Dual ℝ E) :
    realShearCovector e S p (h+k)=realShearCovector e S p h+realShearCovector e S p k := by
  ext x
  simp only [realShearCovector,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  ring
lemma realShearCovector_smul (t : ℝ) (h : Module.Dual ℝ E) :
    realShearCovector e S p (t • h)=t • realShearCovector e S p h := by
  ext x
  simp only [realShearCovector,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  ring
include hS hcomp in
lemma realShearCovector_incoming (r : M) :
    realShearCovector e S p (S.flip (e r))=S.flip (e (mutationShear Ω p r)) := by
  have hs : ∀a b,S a b= -S b a:=by
    intro a b
    have H:=hS (a+b)
    simp only [map_add,LinearMap.add_apply,hS] at H
    linarith
  ext x
  change S x (e r)+S (e p) (e r)*S (e p) x=S x (e (r-Ω p r • p))
  rw [map_sub,map_zsmul,map_sub,map_zsmul,hcomp,hs x (e p)]
  simp only [zsmul_eq_mul]
  ring
include hS hcomp in
lemma realShearCovector_incidence (h : Module.Dual ℝ E) (m : M) :
    realShearCovector e S p h (e (mutationShear Ω p m))=h (e m) := by
  have hp : Ω p p=0:=by
    have H:=hS (e p)
    rw [hcomp] at H
    exact_mod_cast H
  change ((realShearCovector e S p h).toAddMonoidHom.comp e) (mutationShear Ω p m)=_
  rw [realShearCovector_lattice Ω e S p hcomp]
  change h (e (mutationShearInverse Ω p (mutationShear Ω p m)))=_
  rw [mutationShear_left_inverse Ω p hp]

def realSideCovector (pos : Bool) (h : Module.Dual ℝ E) : Module.Dual ℝ E :=
  if pos then h else realShearCovector e S p h
lemma realMutationCovector_eq_side (pos : Bool) (h : Module.Dual ℝ E)
    (hside : if pos then 0≤h (e p) else h (e p)≤0) :
    realMutationCovector e S p h=realSideCovector e S p pos h := by
  cases pos
  · change h (e p)≤0 at hside
    change (if 0≤h (e p) then h else realShearCovector e S p h)=realShearCovector e S p h
    by_cases hh : 0≤h (e p)
    · rw [ite_eq_left hh,realShearCovector,le_antisymm hside hh,zero_smul,add_zero]
    · rw [ite_eq_right hh]
  · change 0≤h (e p) at hside
    exact ite_eq_left hside

include hS hcomp in
lemma realSideCovector_incoming_line (pos : Bool) (k : Module.Dual ℝ E) (r : M) (t : ℝ) :
    realSideCovector e S p pos (k+t • S.flip (e r))=
      realSideCovector e S p pos k+t • S.flip (e (if pos then r else mutationShear Ω p r)) := by
  cases pos
  · change realShearCovector e S p (k+t • S.flip (e r))=
      realShearCovector e S p k+t • S.flip (e (mutationShear Ω p r))
    rw [realShearCovector_add,realShearCovector_smul,realShearCovector_incoming Ω e S p hS hcomp]
  · rfl
include hS hcomp in
lemma realSideCovector_incidence (pos : Bool) (h : Module.Dual ℝ E) (r : M) :
    realSideCovector e S p pos h (e (if pos then r else mutationShear Ω p r))=h (e r) := by
  cases pos
  · exact realShearCovector_incidence Ω e S p hS hcomp h r
  · rfl
include hS hcomp in
lemma realMutationCovector_incoming_line (pos : Bool) (k : Module.Dual ℝ E) (r : M) (t : ℝ)
    (hside : if pos then 0≤(k+t • S.flip (e r)) (e p) else (k+t • S.flip (e r)) (e p)≤0) :
    realMutationCovector e S p (k+t • S.flip (e r))=
      realSideCovector e S p pos k+t • S.flip (e (if pos then r else mutationShear Ω p r)) := by
  rw [realMutationCovector_eq_side e S p pos _ hside]
  exact realSideCovector_incoming_line Ω e S p hS hcomp pos k r t
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I) (pos : Bool)
omit [Fintype I] in
lemma mutationLinearPiece_positive_ray (r m : M) (hr : OnPositiveRay r m) :
    OnPositiveRay (mutationLinearPiece Ω C pc pos r) (mutationLinearPiece Ω C pc pos m) := by
  obtain ⟨a,b,ha,hb,he⟩:=hr
  refine ⟨a,b,ha,hb,?_⟩
  simpa only [map_nsmul] using congrArg (mutationLinearPiece Ω C pc pos) he

variable {R : Type*} [CommRing R] (v : Rˣ)
local instance geometricMutationLinesRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance geometricMutationLinesAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance geometricMutationLinesAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma mutationCompletion_ray_support (f : PowerSeries (Torus v Ω)) (hc : constantCoeff f=1)
    (r : M) (hr : ∀n m,coeff (n+1) f m≠0 → OnPositiveRay r m) :
    ∀d m,coeff (d+1) (mutationCompletion Ω hΩ C coord pc pos v f) m≠0 →
      OnPositiveRay (mutationLinearPiece Ω C pc pos r) m := by
  classical
  intro d m hm
  obtain ⟨a,rfl⟩:=mutationLinearPiece_surjective Ω hΩ C pc pos m
  rw [mutationCompletion_coeff_read] at hm
  split_ifs at hm with hd
  · obtain ⟨n,hn,hna⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
    cases n with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply,hc] at hna
      have ha : a=0:=by
        by_contra hh
        exact hna (Finsupp.single_eq_of_ne hh)
      rw [ha,map_zero,Int.toNat_zero] at hd
      omega
    | succ n =>exact mutationLinearPiece_positive_ray Ω C pc pos r a (hr n a hna)
  · exact (hm rfl).elim

variable (hcoord : ∀d,coord (C d)=d)
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
lemma actualMutatedWall_ray_support (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀d m,coeff (d+1) (actualMutatedWall Ω hΩ C coord hcoord pc pos e he S hS hcomp L hdeg
      r dr hdr hrd h hg hside).val m≠0 → OnPositiveRay (mutationLinearPiece Ω C pc pos r) m := by
  apply mutationCompletion_ray_support Ω hΩ C coord pc pos LaurentRay.vUnit _
    (chartZero LaurentRay.vUnit Ω C _ (simpleTotalTransport Ω C)).property.1 r
  intro n m hm
  by_contra HH
  exact hm ((hg (n+1)).ray_supported LaurentRay.vUnit Ω C (simpleTotalTransport Ω C)
    (n+1) (by omega) le_rfl m HH)

omit [Fintype I] in
include hS hcomp in
lemma realSideCovector_mutated_incidence (h : Module.Dual ℝ E) (r : M) :
    realSideCovector e S (simpleRoot C pc) pos h (e (mutationLinearPiece Ω C pc pos r))=h (e r) := by
  cases pos
  · exact realShearCovector_incidence Ω e S (simpleRoot C pc) hS hcomp h r
  · rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
