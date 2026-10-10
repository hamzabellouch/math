import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.LatticeHahn
import OAI.Combinatorics.Chromatic.Walls.PolynomialAdjointCoefficients
import OAI.Combinatorics.Chromatic.GradedAlgebra.PureCoefficient

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber
noncomputable section
variable {M:Type*} [AddCommGroup M]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (τ:M →+ ℤ)
local instance pureActualCoefficientsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance pureActualCoefficientsAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

include hΩ in
lemma actualMonomialAdjointCoefficient_read (f:PowerSeries (Torus LaurentRay.vUnit Ω)) (b m:M) :
    actualMonomialAdjointCoefficient Ω τ f b m=
      if 0≤τ (m-b) then
        coeff (τ (m-b)).toNat (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m else 0 := by
  unfold actualMonomialAdjointCoefficient actualRootCoefficient
  split_ifs with h
  · simpa only [sub_add_cancel] using
      (adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ f b (m-b) (τ (m-b)).toNat).symm
  · exact zero_mul _

include hΩ in
lemma normalizedSimple_adjoint_coefficient (p b:M) (j:ℕ) :
    coeff j (adjoint (normalizedSimple Ω p) (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b)))=
      Torus.monomial LaurentRay.vUnit Ω (b+j • p) (coeff j (centeredRatio LaurentRay.vUnit (Ω p b))) := by
  rw [adjoint,normalizedSimple_inverse Ω hΩ p]
  have H:=old_pure_coeff LaurentRay.vUnit Ω hΩ p b j
  simpa only [rayUnit,normalizedSimple,←shiftedElementary_zero,laurent_shiftedElementary_zero] using H

include hΩ in
lemma actual_pure_monomial (k:M →+ ℤ) (p:M) (hp:k p=1) (hτ:τ p=1) (b m:M) :
    actualMonomialAdjointCoefficient Ω τ (normalizedSimple Ω p) b m=
      readFiber LaurentRay.vUnit Ω k p hp m
        (pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
          (embed LaurentRay.vUnit Ω hΩ k p hp (Torus.X LaurentRay.vUnit Ω b))) := by
  classical
  have hq:∀n:ℕ,1-(↑(LaurentRay.vUnit^(-2:ℤ)):LaurentSeries ℚ)^(n+1)≠0:=by
    intro n
    rw [LaurentRay.vUnit_zpow]
    exact UnitSelections.laurent_q_not_root n
  by_cases hm:∃j:ℕ,m=b+j • p
  · obtain ⟨j,rfl⟩:=hm
    rw [actualMonomialAdjointCoefficient_read Ω hΩ τ]
    have ht:τ (b+j • p-b)=(j:ℤ):=by simp only [map_sub,map_add,map_nsmul,hτ,nsmul_eq_mul,mul_one]; omega
    rw [ht,ite_eq_left (Int.natCast_nonneg j),Int.toNat_natCast,normalizedSimple_adjoint_coefficient Ω hΩ,
      read_pure_monomial_shift LaurentRay.vUnit Ω hΩ k p hp hq]
    exact Finsupp.single_eq_same
  · rw [actualMonomialAdjointCoefficient_read Ω hΩ τ]
    have hr:readFiber LaurentRay.vUnit Ω k p hp m
        (pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
          (embed LaurentRay.vUnit Ω hΩ k p hp (Torus.X LaurentRay.vUnit Ω b)))=0:=by
      by_contra hh
      exact hm (read_pure_monomial_support LaurentRay.vUnit Ω hΩ k p hp hq b m hh)
    rw [hr]
    split_ifs
    · rw [normalizedSimple_adjoint_coefficient Ω hΩ]
      exact Finsupp.single_eq_of_ne (fun he=>hm ⟨_,he⟩)
    · rfl
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries HahnSeries
noncomputable section
variable {A:Type*} [Ring A]
def hahnAction (f:PowerSeries A) (x:HahnSeries ℤ A) : HahnSeries ℤ A :=
  ofPowerSeries ℤ A f*x*ofPowerSeries ℤ A (invOfUnit f 1)
lemma hahnAction_add (f:PowerSeries A) (x y:HahnSeries ℤ A) :
    hahnAction f (x+y)=hahnAction f x+hahnAction f y := by
  simp only [hahnAction,mul_add,add_mul]
lemma hahnAction_zero (f:PowerSeries A) : hahnAction f (0:HahnSeries ℤ A)=0 := by
  simp only [hahnAction,mul_zero,zero_mul]
lemma hahnAction_one (x:HahnSeries ℤ A) : hahnAction 1 x=x := by
  have hi:invOfUnit (1:PowerSeries A) 1=1:=by simpa using mul_invOfUnit (1:PowerSeries A) 1 (by simp)
  simp only [hahnAction,hi,map_one,one_mul,mul_one]
lemma hahnAction_mul (f g:PowerSeries A) (x:HahnSeries ℤ A)
    (hf:constantCoeff f=1) (hg:constantCoeff g=1) :
    hahnAction (f*g) x=hahnAction f (hahnAction g x) := by
  simp only [hahnAction,inverse_mul f g hf hg,map_mul,mul_assoc]
lemma hahnAction_inverse_cancel (f:PowerSeries A) (x:HahnSeries ℤ A)
    (hf:constantCoeff f=1) : hahnAction (invOfUnit f 1) (hahnAction f x)=x := by
  rw [←hahnAction_mul _ _ _ (by simp) hf,invOfUnit_mul f 1 hf,hahnAction_one]
lemma ofPowerSeries_coeff_int (f:PowerSeries A) (j:ℤ) :
    (ofPowerSeries ℤ A f).coeff j=if 0≤j then coeff j.toNat f else 0 := by
  by_cases hj:0≤j
  · rw [ite_eq_left hj,←Int.toNat_of_nonneg hj,HahnSeries.ofPowerSeries_apply_coeff,Int.toNat_natCast]
  · rw [ite_eq_right hj,HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨n,_,hn⟩
    have he:(n:ℤ)=j:=hn
    omega
end
end ElementaryPositivity.PowerSeriesAdjoint
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0) (τ:M →+ ℤ)
local instance pureActualScalarCoefficientsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance pureActualScalarCoefficientsAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance pureActualScalarCoefficientsNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

lemma adjoint_scalar_monomial_coeff (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (b m:M) (c:LaurentSeries ℚ) (n:ℕ) :
    coeff n (adjoint f (PowerSeries.C (Torus.monomial LaurentRay.vUnit Ω b c))) m=
      c*coeff n (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m := by
  rw [adjoint_torus_expansion]
  change (Finsupp.single b c).sum (fun d a=>a*coeff n (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω d))) m)=_
  exact Finsupp.sum_single_index (zero_mul _)

lemma hahnAction_monomial_coeff (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (b m:M) (c:LaurentSeries ℚ) (j:ℤ) :
    (hahnAction f (latticeHahn LaurentRay.vUnit Ω τ (Torus.monomial LaurentRay.vUnit Ω b c))).coeff j m=
      if 0≤j-τ b then c*coeff (j-τ b).toNat (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m else 0 := by
  rw [latticeHahn_monomial,hahnAction,hahn_single_shift_adjoint,
    HahnSeries.coeff_single_mul,one_mul,ofPowerSeries_coeff_int]
  split_ifs
  · exact adjoint_scalar_monomial_coeff Ω f b m c _
  · rfl

include hΩ in
lemma hahnAction_actual_coeff (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    (hahnAction f (latticeHahn LaurentRay.vUnit Ω τ F)).coeff (τ m) m=
      actualPolynomialAdjointCoefficient Ω τ f F m := by
  classical
  induction F using Finsupp.induction_linear with
  | zero=>simp [hahnAction_zero,actualPolynomialAdjointCoefficient]
  | add F G hF hG=>rw [map_add,hahnAction_add,HahnSeries.coeff_add,
      Finsupp.add_apply,actualPolynomialAdjointCoefficient_add,hF,hG]
  | single b c=>
    change (hahnAction f (latticeHahn LaurentRay.vUnit Ω τ (Torus.monomial LaurentRay.vUnit Ω b c))).coeff (τ m) m=
      actualPolynomialAdjointCoefficient Ω τ f (Torus.monomial LaurentRay.vUnit Ω b c) m
    rw [hahnAction_monomial_coeff,actualPolynomialAdjointCoefficient_monomial,
      actualMonomialAdjointCoefficient_read Ω hΩ τ,map_sub]
    split_ifs <;> simp

omit [DecidableEq I] in
include hΩ in
lemma adjoint_monomial_degree (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
    (hcoord:∀d,coord (C d)=d) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (b m:M) (n:ℕ)
    (hm:coeff n (adjoint f.val (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m≠0) :
    rootOrder coord (m-b)=(n:ℤ) := by
  have H:=normalizedMonomialAction_graded LaurentRay.vUnit Ω hΩ C f b
  have he:=adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ f.val b (m-b) n
  simp only [sub_add_cancel] at he
  rw [he] at hm
  apply rootOrder_eq C coord hcoord
  by_contra hh
  exact hm (by rw [H n (m-b) hh,zero_mul])

omit [DecidableEq I] in
include hΩ in
lemma hahnAction_diagonal (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
    (hcoord:∀d,coord (C d)=d) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (F:Torus LaurentRay.vUnit Ω) (j:ℤ) (m:M) (hj:j≠rootOrder coord m) :
    (hahnAction f.val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) F)).coeff j m=0 := by
  classical
  induction F using Finsupp.induction_linear with
  | zero=>simp [hahnAction_zero]
  | add F G hF hG=>rw [map_add,hahnAction_add,HahnSeries.coeff_add,Finsupp.add_apply,hF,hG,add_zero]
  | single b c=>
    change (hahnAction f.val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) (Torus.monomial LaurentRay.vUnit Ω b c))).coeff j m=0
    rw [hahnAction_monomial_coeff]
    split_ifs with hn
    · have hz:coeff (j-rootOrder coord b).toNat
          (adjoint f.val (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m=0:=by
        by_contra hh
        have H:=adjoint_monomial_degree Ω hΩ C coord hcoord f b m _ hh
        rw [map_sub,Int.toNat_of_nonneg hn] at H
        exact hj (by omega)
      rw [hz,mul_zero]
    · rfl

omit [DecidableEq I] in
include hΩ in
lemma hahnAction_finite_iff (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
    (hcoord:∀d,coord (C d)=d) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (F G:Torus LaurentRay.vUnit Ω) :
    hahnAction f.val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) F)=
        latticeHahn LaurentRay.vUnit Ω (rootOrder coord) G ↔
      ∀m,actualPolynomialAdjointCoefficient Ω (rootOrder coord) f.val F m=G m := by
  constructor
  · intro h m
    have H:=congrArg (fun x:HahnSeries ℤ (Torus LaurentRay.vUnit Ω)=>x.coeff (rootOrder coord m) m) h
    simpa only [hahnAction_actual_coeff Ω hΩ,latticeHahn_coeff,ite_true] using H
  · intro h
    apply HahnSeries.ext
    funext j
    apply Finsupp.ext
    intro m
    by_cases hj:j=rootOrder coord m
    · subst j
      rw [hahnAction_actual_coeff Ω hΩ,latticeHahn_coeff,ite_eq_left rfl,h]
    · rw [hahnAction_diagonal Ω hΩ C coord hcoord f F j m hj,latticeHahn_coeff,ite_eq_right hj]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
