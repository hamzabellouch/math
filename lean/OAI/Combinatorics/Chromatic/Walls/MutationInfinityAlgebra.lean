import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationOrientedCompatibility
import OAI.Combinatorics.Chromatic.QuantumTorus.InfinityExpansionFaithful
import OAI.Combinatorics.Chromatic.Walls.MutationLaurentCompletion
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentRegradePure

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RationalFiber WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (v : (LaurentSeries ℚ)ˣ)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

lemma infinityCompletedUnit_mul
    (F G H : CompletedPositive v Ω (mutatedRoots Ω C pc))
    (h : H.val=F.val*G.val) :
    infinityCompletedUnit Ω C coord hcoord pc v H=
      infinityCompletedUnit Ω C coord hcoord pc v F*
      infinityCompletedUnit Ω C coord hcoord pc v G := by
  apply Units.ext
  change laurentRegrade v Ω _ _ _ H.val _=_
  have Hsub : (completedInfinityUnit Ω C coord hcoord pc v H).val=
      (completedInfinityUnit Ω C coord hcoord pc v F).val*
      (completedInfinityUnit Ω C coord hcoord pc v G).val := Subtype.ext h
  exact congrArg (laurentRegradeHom v Ω _ _ _) Hsub |>.trans (map_mul _ _ _)

lemma infinityCompletedUnit_one (F : CompletedPositive v Ω (mutatedRoots Ω C pc))
    (h : F.val=1) : infinityCompletedUnit Ω C coord hcoord pc v F=1 := by
  apply Units.ext
  change laurentRegrade v Ω _ _ _ F.val _=1
  have Hsub : (completedInfinityUnit Ω C coord hcoord pc v F).val=1:=Subtype.ext h
  exact congrArg (laurentRegradeHom v Ω _ _ _) Hsub |>.trans (map_one _)

lemma infinityCompletedUnit_inverse
    (F G : CompletedPositive v Ω (mutatedRoots Ω C pc))
    (h : G.val=invOfUnit F.val 1) :
    infinityCompletedUnit Ω C coord hcoord pc v G=
      (infinityCompletedUnit Ω C coord hcoord pc v F)⁻¹ := by
  apply Units.ext
  change mutatedLaurent Ω C coord hcoord pc v G=
    mutatedLaurent Ω C coord hcoord pc v (completedInverse v Ω (mutatedRoots Ω C pc) F)
  exact congrArg _ (Subtype.ext h)

lemma mutatedLaurent_coeff_congr
    (F G : CompletedPositive v Ω (mutatedRoots Ω C pc)) (d : ℕ) (z : ℤ)
    (h : ∀n≤(z+(mutationSize Ω C pc+1:ℤ)*(d:ℤ)).toNat,coeff n F.val=coeff n G.val) :
    (coeff d (mutatedLaurent Ω C coord hcoord pc v F)).coeff z=
      (coeff d (mutatedLaurent Ω C coord hcoord pc v G)).coeff z := by
  exact laurentRegrade_coeff_congr v Ω _ _ _
    (mutated_series_laurentBounded Ω C coord hcoord pc v F.property.2)
    (mutated_series_laurentBounded Ω C coord hcoord pc v G.property.2) d z h

lemma infinityCompletedUnit_pure (hΩ : ∀m,Ω m m=0)
    (F : CompletedPositive v Ω (mutatedRoots Ω C pc))
    (h : F.val=raySeries v Ω (-simpleRoot C pc) (shiftedElementary v 0)) :
    infinityCompletedUnit Ω C coord hcoord pc v F=
      completedPureUnit v Ω hΩ (-simpleRoot C pc) := by
  have hd : nonpDegree (mutatedCoordinates Ω C coord pc) pc (-simpleRoot C pc)=0 := by
    rw [←mutatedRoot_p Ω C pc]
    exact nonpDegree_simple_self (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      (mutatedCoordinates_retraction Ω C coord hcoord pc) pc
  have hk : (-pureDegree coord pc) (-simpleRoot C pc)=1 := by
    simp only [AddMonoidHom.neg_apply,map_neg,neg_neg,pureDegree_simple_self C coord hcoord pc]
  apply Units.ext
  change laurentRegrade v Ω _ _ _ F.val _=PowerSeries.C _
  have H:=laurentRegrade_pure v Ω
    (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (-pureDegree coord pc)
    (mutationSize Ω C pc) (-simpleRoot C pc) hd hk (shiftedElementary v 0)
  calc
    _ = PowerSeries.C (HahnSeries.ofPowerSeries ℤ (Torus v Ω)
        (raySeries v Ω (-simpleRoot C pc) (shiftedElementary v 0))) := by
      convert H using 1
      congr 1
    _ = _ := by
      congr 1
      exact (purePower_eq v Ω hΩ (-simpleRoot C pc) (shiftedElementary v 0)).symm
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma completed_expand_opposite
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      ((completedOppositeInverseAction v _ _).symm f)=
    innerHom (completedPureUnit v Ω hΩ (-p))
      (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) f) := by
  have H:=completed_expand_opposite_inverse v Ω hΩ k p hq
    ((completedOppositeInverseAction v _ _).symm f)
  rw [RingEquiv.apply_symm_apply] at H
  have HH:=congrArg (innerHom (completedPureUnit v Ω hΩ (-p))) H
  rw [innerHom_cancel_inv] at HH
  exact HH.symm
end
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma mutation_infinity_oriented_coefficient (b : Bool) (f : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (d : ℕ) (m : M) :
    ((coeff d (PowerSeries.map (expandFiberInfinity LaurentRay.vUnit Ω hΩ
        (pureDegree coord pc) (simpleRoot C pc))
      (mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
        (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω) pos
        (rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
          (pureDegree_simple_self C coord hcoord pc) (nonpDegree coord pc) (mutationSize Ω C pc+1)
          (orientPowerSeries b f.val))))).coeff (-pureDegree coord pc m)) m=
    coeff d (regrade LaurentRay.vUnit Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
      (mutationSize Ω C pc+1) (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (orientPowerSeries b f.val))) m := by
  rw [coeff_map,expandFiberInfinity_read LaurentRay.vUnit Ω hΩ (pureDegree coord pc)
    (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)]
  rw [mutation_rational_oriented_compatibility Ω hΩ C coord hcoord pc pos b f hf,
    rationalRegrade,coeff_map]
  exact readFiberInfinity_embedAdd LaurentRay.vUnit Ω _ _ _ _ _
end
end ElementaryPositivity.RationalFiber

end

end OAI
