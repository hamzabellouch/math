import Mathlib
import OAI.Combinatorics.Chromatic.Walls.InfinityPath

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) :=
  (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

lemma actualInfinityPath_loop_commute {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (d N : ℕ) (hN : 1≤N) (hdN : (mutationSize Ω C pc+1)*d≤N) (m : M) :
    coeff d ((actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N).val*
      PowerSeries.C (HahnSeries.single (-pureDegree coord pc m) (Torus.X LaurentRay.vUnit Ω m)))=
    coeff d (PowerSeries.C (HahnSeries.single (-pureDegree coord pc m) (Torus.X LaurentRay.vUnit Ω m))*
      (actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N).val) := by
  classical
  let pos:=decide (0<a (e (simpleRoot C pc)))
  let x:=infinityTestInput LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
    (pureDegree_simple_self C coord hcoord pc) pos m
  have hs:=actualInfinityPath_product_square Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N hN x
  have ht:=infinitySideHom_test LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
    (pureDegree_simple_self C coord hcoord pc) pos m
  apply coeff_commute_of_adjoints
  intro j hj
  rw [←ht]
  rw [hs]
  apply infinitySideHom_coeff_congr
  rw [←actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p x j N hN
    ((Nat.mul_le_mul_left _ hj).trans hdN)]
  rw [actualPathAction_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p x]

lemma actualInfinityPath_loop_row_commute {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (d N : ℕ) (hN : 1≤N) (hdN : (mutationSize Ω C pc+1)*d≤N) (z : ℤ) (m : M) :
    ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit
      (mutatedPathProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N))).coeff z)*
      Torus.X LaurentRay.vUnit Ω m=
    Torus.X LaurentRay.vUnit Ω m*
      ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit
      (mutatedPathProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N))).coeff z) := by
  have H:=congrArg (fun f : HahnSeries ℤ (Torus LaurentRay.vUnit Ω)=>f.coeff (z-pureDegree coord pc m))
    (actualInfinityPath_loop_commute Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p d N hN hdN m)
  rw [coeff_mul_C,coeff_C_mul,HahnSeries.coeff_mul_single,HahnSeries.coeff_single_mul] at H
  have heq : z-pureDegree coord pc m-(-pureDegree coord pc m)=z:=by omega
  rw [heq] at H
  exact H
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M I : Type*} [Field K] [AddCommGroup M] [Fintype I]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

lemma positive_root_ne_zero (hC : Function.Injective C) {n : ℕ} (hn : 0<n)
    (h : HasRootDegree C n (0:M)) : False := by
  obtain ⟨d,hd,hc⟩:=h
  have hz : (fun i=>(d i:ℤ))=0:=hC (hc.trans (map_zero C).symm)
  have hd0 : d=0:=by
    funext i
    have H:=congrFun hz i
    change (d i:ℤ)=0 at H
    change d i=0
    exact_mod_cast H
  have hn0 : n=0:=by simpa only [hd0,Pi.zero_apply,Finset.sum_const_zero] using hd.symm
  omega

lemma completed_central_through
    (hv : Function.Injective (fun z : ℤ=>(↑(v^z):K)))
    (hΩ : ∀m,Ω m m=0) (hnd : ∀r≠0,∃m,Ω r m≠0) (hC : Function.Injective C)
    (F : CompletedPositive v Ω C) (N : ℕ)
    (hf : ∀m n,n≤N → coeff n (F.val*PowerSeries.C (Torus.X v Ω m))=
      coeff n (PowerSeries.C (Torus.X v Ω m)*F.val)) :
    ∀n≤N,coeff n F.val=coeff n 1 := by
  intro n hn
  by_cases hn0 : n=0
  · subst n
    simpa only [coeff_zero_eq_constantCoeff,map_one] using F.property.1
  · have hc : ∀m,coeff n F.val*Torus.X v Ω m=Torus.X v Ω m*coeff n F.val:=by
      intro m
      simpa only [coeff_mul_C,coeff_C_mul] using hf m n hn
    rw [coeff_one,ite_eq_right hn0]
    apply Finsupp.ext
    intro r
    by_cases hr : r=0
    · subst r
      exact F.property.2 n 0 (positive_root_ne_zero C hC (Nat.pos_of_ne_zero hn0))
    · exact central_support_zero v Ω hv hΩ hnd (coeff n F.val) hc r hr

lemma completed_adjoint_faithful_through
    (hv : Function.Injective (fun z : ℤ=>(↑(v^z):K)))
    (hΩ : ∀m,Ω m m=0) (hnd : ∀r≠0,∃m,Ω r m≠0) (hC : Function.Injective C)
    (F : CompletedPositive v Ω C) (N : ℕ)
    (hf : ∀m n,n≤N → coeff n (F.val*PowerSeries.C (Torus.X v Ω m)*invOfUnit F.val 1)=
      coeff n (PowerSeries.C (Torus.X v Ω m))) :
    ∀n≤N,coeff n F.val=coeff n 1 := by
  apply completed_central_through v Ω C hv hΩ hnd hC F N
  intro m n hn
  have H:=FormalLog.mul_coeff_congr
    (F.val*PowerSeries.C (Torus.X v Ω m)*invOfUnit F.val 1)
    F.val (PowerSeries.C (Torus.X v Ω m)) F.val n
    (fun j hj=>hf m j (hj.trans hn)) (fun _ _=>rfl)
  simpa only [mul_assoc,invOfUnit_mul F.val 1 F.property.1,mul_one] using H

lemma completed_adjoint_faithful
    (hv : Function.Injective (fun z : ℤ=>(↑(v^z):K)))
    (hΩ : ∀m,Ω m m=0) (hnd : ∀r≠0,∃m,Ω r m≠0) (hC : Function.Injective C)
    (F : CompletedPositive v Ω C)
    (hf : ∀m,F.val*PowerSeries.C (Torus.X v Ω m)*invOfUnit F.val 1=
      PowerSeries.C (Torus.X v Ω m)) : F.val=1 := by
  apply PowerSeries.ext
  intro n
  exact completed_adjoint_faithful_through v Ω C hv hΩ hnd hC F n
    (fun m j _=>congrArg (coeff j) (hf m)) n le_rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
