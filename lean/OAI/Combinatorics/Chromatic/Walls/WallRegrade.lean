import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpRegradeFaithful
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationDegreeBound

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d)
def rootOrder : M →+ ℤ where
  toFun m:=∑i,coord m i
  map_zero':=by simp
  map_add':=by intro a b; simp [Finset.sum_add_distrib]
omit [DecidableEq I] in
include hcoord in
lemma rootOrder_eq {n : ℕ} {m : M} (hm : HasRootDegree C n m) : rootOrder coord m=(n:ℤ) := by
  obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
  change (∑i,coord m i)=(n:ℤ)
  simp only [hc,←Nat.cast_sum,hd]

variable {R : Type*} [CommRing R] [Algebra ℚ R] (v : Rˣ) (Ω : M →+ M →+ ℤ)
omit [Algebra ℚ R] [DecidableEq I] in
include hcoord in
lemma chart_full_homogeneous (h : M →+ ℝ) (f : CompletedPositive v Ω C) :
    FullHomogeneous v Ω (rootOrder coord) (chartZero v Ω C h f).val := by
  intro j m hm
  exact rootOrder_eq C coord hcoord (chart_root_of_ne v Ω C (chartZero v Ω C h f) j m hm)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (pc : I) (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hS hcomp hdeg in
lemma simple_regrade_bound (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (nonpDegree coord pc) (mutationSize Ω C pc+1)
      (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val := by
  intro j m hm
  have hroot:=chart_root_of_ne LaurentRay.vUnit Ω C (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)) j m hm
  have hb:=simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg
    r dr hdr hrd h hg pos hside j m hm
  have H:=fiber_full_degree_bound Ω C coord hcoord pc pos hroot hb
  have hn:=nonpDegree_root_nonneg C coord hcoord pc hroot
  refine ⟨hn,?_⟩
  have hd : ((nonpDegree coord pc m).toNat:ℤ)=nonpDegree coord pc m:=Int.toNat_of_nonneg hn
  rw [←hd] at H
  exact_mod_cast H

include hcoord he hS hcomp hdeg in
lemma simple_inverse_regrade_bound (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (nonpDegree coord pc) (mutationSize Ω C pc+1)
      (PowerSeries.invOfUnit
        (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val 1) :=
  (simple_regrade_bound C coord hcoord Ω pc e he S hS hcomp L hdeg r dr hdr hrd h hg pos hside).invOfUnit
    LaurentRay.vUnit Ω (nonpDegree coord pc) (mutationSize Ω C pc+1)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)

def mutationPieceEquiv : M ≃+ M :=
  if pos then AddEquiv.refl M else mutationShearEquiv Ω (simpleRoot C pc) (hΩ _)
lemma mutationPieceEquiv_apply (m : M) :
    mutationPieceEquiv Ω hΩ C pc pos m=mutationLinearPiece Ω C pc pos m := by
  cases pos <;> rfl
include hΩ in
lemma mutationLinearPiece_pairing (a b : M) :
    Ω (mutationLinearPiece Ω C pc pos a) (mutationLinearPiece Ω C pc pos b)=Ω a b := by
  cases pos
  · exact mutationShear_pairing Ω hΩ _ a b
  · rfl
include hΩ in
lemma mutationLinearPiece_injective : Function.Injective (mutationLinearPiece Ω C pc pos) := by
  intro a b hab
  apply (mutationPieceEquiv Ω hΩ C pc pos).injective
  simpa only [mutationPieceEquiv_apply] using hab
include hΩ in
lemma mutationLinearPiece_surjective : Function.Surjective (mutationLinearPiece Ω C pc pos) := by
  intro m
  refine ⟨(mutationPieceEquiv Ω hΩ C pc pos).symm m,?_⟩
  rw [←mutationPieceEquiv_apply Ω hΩ C pc pos,AddEquiv.apply_symm_apply]

variable [Fintype I]

def mutationNewOrder : M →+ ℤ :=
  (rootOrder (mutatedCoordinates Ω C coord pc)).comp (mutationLinearPiece Ω C pc pos)

include hcoord in
lemma mutationNewOrder_of_root {n : ℕ} {m : M}
    (hm : HasRootDegree (mutatedRoots Ω C pc) n (mutationLinearPiece Ω C pc pos m)) :
    mutationNewOrder Ω C coord pc pos m=(n:ℤ) :=
  rootOrder_eq (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
    (mutatedCoordinates_retraction Ω C coord hcoord pc) hm

variable {R : Type*} [CommRing R] (v : Rˣ)
local instance wallRegradeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance wallRegradeAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance wallRegradeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def mutationTorusPush : Torus v Ω →+* Torus v Ω :=
  Torus.push v Ω Ω (mutationLinearPiece Ω C pc pos) (mutationLinearPiece_pairing Ω hΩ C pc pos)
omit [Fintype I] in
lemma mutationTorusPush_read (f : Torus v Ω) (m : M) :
    mutationTorusPush Ω hΩ C pc pos v f (mutationLinearPiece Ω C pc pos m)=f m :=
  Finsupp.mapDomain_apply_of_injective (mutationLinearPiece_injective Ω hΩ C pc pos) f m

def mutationCompletion (f : PowerSeries (Torus v Ω)) : PowerSeries (Torus v Ω) :=
  PowerSeries.map (mutationTorusPush Ω hΩ C pc pos v)
    (regrade v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f)

lemma mutationCompletion_coeff_read (f : PowerSeries (Torus v Ω)) (d : ℕ) (m : M) :
    coeff d (mutationCompletion Ω hΩ C coord pc pos v f) (mutationLinearPiece Ω C pc pos m)=
      if d=(mutationNewOrder Ω C coord pc pos m).toNat then
        ∑n∈Finset.range ((mutationSize Ω C pc+1)*d+1),coeff n f m else 0 := by
  rw [mutationCompletion,coeff_map,mutationTorusPush_read,regrade_coeff_eval]

include hcoord hΩ in
lemma mutationCompletion_bound (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f.val := by
  intro n m hm
  obtain ⟨d,hd,hnp,hn⟩:=mutation_root_image_bound Ω C coord hcoord pc hΩ pos
    (by by_contra hh; exact hm (f.property.2 n m hh)) (hf n m hm)
  rw [mutationNewOrder_of_root Ω C coord hcoord pc pos hd]
  exact ⟨Int.natCast_nonneg _,by simpa using hn⟩

include hcoord in
lemma mutationCompletion_graded (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    ∀d,coeff d (mutationCompletion Ω hΩ C coord pc pos v f.val)∈
      rootGrade v Ω (mutatedRoots Ω C pc) d := by
  classical
  intro d m hm
  obtain ⟨a,rfl⟩:=mutationLinearPiece_surjective Ω hΩ C pc pos m
  rw [mutationCompletion_coeff_read]
  split_ifs with ha
  · by_contra hz
    obtain ⟨n,hn,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨d',hd',he⟩:=mutation_root_image Ω C coord hcoord pc hΩ pos
      (by by_contra hh; exact hz (f.property.2 n a hh)) (hf n a hz)
    have he':=mutationNewOrder_of_root Ω C coord hcoord pc pos hd'
    rw [he',Int.toNat_natCast] at ha
    exact hm (ha ▸ hd')
  · rfl

lemma mutationCompletion_constant (f : PowerSeries (Torus v Ω)) (hf : constantCoeff f=1) :
    constantCoeff (mutationCompletion Ω hΩ C coord pc pos v f)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  rw [mutationCompletion,coeff_map,regrade_coeff]
  simp only [mul_zero,zero_add,Finset.sum_range_one,coeff_zero_eq_constantCoeff,hf,
    homogenize_one,map_one]

def mutationCompletedPositive (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    CompletedPositive v Ω (mutatedRoots Ω C pc) :=
  ⟨mutationCompletion Ω hΩ C coord pc pos v f.val,
    mutationCompletion_constant Ω hΩ C coord pc pos v f.val f.property.1,
    mutationCompletion_graded Ω hΩ C coord hcoord pc pos v f hf⟩

lemma mutationCompletion_mul {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f)
    (hg : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) g) :
    mutationCompletion Ω hΩ C coord pc pos v (f*g)=
      mutationCompletion Ω hΩ C coord pc pos v f*mutationCompletion Ω hΩ C coord pc pos v g := by
  unfold mutationCompletion
  rw [regrade_mul v Ω _ _ hf hg,map_mul]
lemma mutationCompletion_one : mutationCompletion Ω hΩ C coord pc pos v 1=1 := by
  rw [mutationCompletion,regrade_one,map_one]
lemma mutationCompletion_inverse_mul {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f)
    (hc : constantCoeff f=1) :
    mutationCompletion Ω hΩ C coord pc pos v (PowerSeries.invOfUnit f 1)*
      mutationCompletion Ω hΩ C coord pc pos v f=1 := by
  rw [←mutationCompletion_mul Ω hΩ C coord pc pos v (hf.invOfUnit v Ω _ _) hf,
    PowerSeries.invOfUnit_mul f 1 hc,mutationCompletion_one]
lemma mutationCompletion_mul_inverse {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f)
    (hc : constantCoeff f=1) :
    mutationCompletion Ω hΩ C coord pc pos v f*
      mutationCompletion Ω hΩ C coord pc pos v (PowerSeries.invOfUnit f 1)=1 := by
  rw [←mutationCompletion_mul Ω hΩ C coord pc pos v hf (hf.invOfUnit v Ω _ _),
    PowerSeries.mul_invOfUnit f 1 hc,mutationCompletion_one]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))

def actualMutatedWall (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  mutationCompletedPositive Ω hΩ C coord hcoord pc pos LaurentRay.vUnit
    (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C))
    (simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg r dr hdr hrd h hg pos hside)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
