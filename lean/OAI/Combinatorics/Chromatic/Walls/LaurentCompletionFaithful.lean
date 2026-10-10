import Mathlib
import OAI.Combinatorics.Chromatic.Walls.InfinityFiniteLoop

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M I : Type*} [Field K] [AddCommGroup M] [Fintype I]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (δ κ η : M →+ ℤ) (B : ℕ)
local instance laurentCompletionFaithfulRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentCompletionFaithfulAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentCompletionFaithfulAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentCompletionFaithfulNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentCompletionFaithfulNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

lemma laurentRegrade_central_faithful
    (hv : Function.Injective (fun z : ℤ=>(↑(v^z):K)))
    (hΩ : ∀m,Ω m m=0) (hnd : ∀r≠0,∃m,Ω r m≠0) (hC : Function.Injective C)
    (F : CompletedPositive v Ω C) (hF : LaurentBounded v Ω δ κ B F.val)
    (hhom : FullHomogeneous v Ω η F.val) (z : M → ℤ)
    (hcentral : ∀m,laurentRegrade v Ω δ κ B F.val hF*
        PowerSeries.C (HahnSeries.single (z m) (Torus.X v Ω m))=
      PowerSeries.C (HahnSeries.single (z m) (Torus.X v Ω m))*
        laurentRegrade v Ω δ κ B F.val hF) : F.val=1 := by
  have hcoeff (d : ℕ) (w : ℤ) :
      ∀m,((coeff d (laurentRegrade v Ω δ κ B F.val hF)).coeff w)*Torus.X v Ω m=
        Torus.X v Ω m*((coeff d (laurentRegrade v Ω δ κ B F.val hF)).coeff w) := by
    intro m
    have H:=congrArg (fun f : PowerSeries (HahnSeries ℤ (Torus v Ω))=>
      (coeff d f).coeff (w+z m)) (hcentral m)
    rw [coeff_mul_C,coeff_C_mul] at H
    rw [HahnSeries.coeff_mul_single_add,HahnSeries.coeff_single_mul_add] at H
    exact H
  apply PowerSeries.ext
  intro n
  by_cases hn : n=0
  · subst n
    simpa only [coeff_zero_eq_constantCoeff,map_one] using F.property.1
  · rw [coeff_one,ite_eq_right hn]
    ext r
    by_cases hr : r=0
    · subst r
      exact F.property.2 n 0 (positive_root_ne_zero C hC (Nat.pos_of_ne_zero hn))
    · by_contra hh
      have hd:=(hF n r hh).1
      have H:=central_support_zero v Ω hv hΩ hnd
        ((coeff (δ r).toNat (laurentRegrade v Ω δ κ B F.val hF)).coeff (κ r))
        (hcoeff (δ r).toNat (κ r)) r hr
      rw [laurentRegrade_read v Ω δ κ η B hF hhom n _ (κ r) r (hhom n r hh)
        (Int.toNat_of_nonneg hd).symm rfl] at H
      exact hh H
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.WallUnits.LaurentRay
lemma vUnit_zpow_injective : Function.Injective (fun z : ℤ=>(↑(vUnit^z):LaurentSeries ℚ)) := by
  intro a b hab
  change (↑(vUnit^a):LaurentSeries ℚ)=↑(vUnit^b) at hab
  rw [vUnit_zpow,vUnit_zpow] at hab
  have H:=congrArg (fun f : LaurentSeries ℚ=>f.coeff (-a)) hab
  by_contra hh
  simp [hh] at H
end ElementaryPositivity.WallUnits.LaurentRay
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma laurent_completed_adjoint_faithful
    (hΩ : ∀m,Ω m m=0) (hnd : ∀r≠0,∃m,Ω r m≠0) (hC : Function.Injective C)
    (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀m,F.val*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F.val 1=
      PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)) : F.val=1 :=
  completed_adjoint_faithful LaurentRay.vUnit Ω C LaurentRay.vUnit_zpow_injective hΩ hnd hC F hf
end
end ElementaryPositivity.QuantumTorus

end
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

lemma mutatedPathCompleted_loop_row_commute {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (d : ℕ) (z : ℤ) (m : M) :
    ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit
      (mutatedPathCompletedPositive Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p))).coeff z)*
      Torus.X LaurentRay.vUnit Ω m=
    Torus.X LaurentRay.vUnit Ω m*
      ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit
      (mutatedPathCompletedPositive Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p))).coeff z) := by
  let D:=(z+(mutationSize Ω C pc+1:ℤ)*(d:ℤ)).toNat
  let N:=max 1 ((mutationSize Ω C pc+1)*max d D)
  have hN : 1≤N:=le_max_left _ _
  have hdN : (mutationSize Ω C pc+1)*d≤N:=
    (Nat.mul_le_mul_left _ (le_max_left d D)).trans (le_max_right _ _)
  have hDN : (mutationSize Ω C pc+1)*D≤N:=
    (Nat.mul_le_mul_left _ (le_max_right d D)).trans (le_max_right _ _)
  let F:=mutatedPathCompletedPositive Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p
  let G:=mutatedPathProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N
  have hc:=mutatedLaurent_coeff_congr Ω C coord hcoord pc LaurentRay.vUnit F G d z
    (mutatedPathCompletion_coeff Ω hΩ C coord pc e he L hdeg p D N hN hDN)
  have HH:=actualInfinityPath_loop_row_commute Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p d N hN hdN z m
  calc
    _ = ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit G)).coeff z)*
        Torus.X LaurentRay.vUnit Ω m := congrArg (fun t=>t*Torus.X LaurentRay.vUnit Ω m) hc
    _ = Torus.X LaurentRay.vUnit Ω m*
        ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit G)).coeff z) := HH
    _ = _ := congrArg (fun t=>Torus.X LaurentRay.vUnit Ω m*t) hc.symm

include hcoord hS hcomp in
lemma mutatedPathCompletion_loop (hnd : ∀r≠0,∃m,Ω r m≠0)
    {a : Module.Dual ℝ E} (p : GenericLinePath C e a a) :
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p=1 := by
  let F:=mutatedPathCompletedPositive Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p
  have hC : Function.Injective (mutatedRoots Ω C pc) :=
    Function.LeftInverse.injective (mutatedCoordinates_retraction Ω C coord hcoord pc)
  refine laurentRegrade_central_faithful LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
    (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (-pureDegree coord pc)
    (rootOrder (mutatedCoordinates Ω C coord pc)) (mutationSize Ω C pc)
    LaurentRay.vUnit_zpow_injective hΩ hnd hC F
    (mutated_series_laurentBounded Ω C coord hcoord pc LaurentRay.vUnit F.property.2)
    (completed_full_homogeneous LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedCoordinates Ω C coord pc) (mutatedCoordinates_retraction Ω C coord hcoord pc) F)
    (fun m=> -pureDegree coord pc m) ?_
  intro m
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ext
  funext z
  rw [coeff_mul_C,coeff_C_mul,HahnSeries.coeff_mul_single,HahnSeries.coeff_single_mul]
  exact mutatedPathCompleted_loop_row_commute Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p d _ m
end
end ElementaryPositivity.RationalFiber

end

end OAI
