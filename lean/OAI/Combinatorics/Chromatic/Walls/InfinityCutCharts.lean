import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.InfinityLaurentFinite
import OAI.Combinatorics.Chromatic.QuantumTorus.InfinityUnitAlgebra
import OAI.Combinatorics.Chromatic.Walls.MutationInfinityAlgebra

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def infinitySideHom (pos : Bool) :
    PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) →+*
    PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  (PowerSeries.map (expandFiberInfinity v Ω hΩ k p)).comp
    (mutationSideAction v (complementOmega k Ω) (complementAlpha k p Ω) pos).toRingHom

lemma infinitySide_cut (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    innerHom (completedPureUnit v Ω hΩ (-p))⁻¹ (infinitySideHom v Ω hΩ k p true f)=
      infinitySideHom v Ω hΩ k p false (completedPureAction v _ _ f) := by
  change innerHom _ (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) f)=_
  rw [←completed_expand_opposite_inverse v Ω hΩ k p hq]
  change PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
    (completedOppositeInverseAction v _ _ f)=
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (mutationSideAction v _ _ false (completedPureAction v _ _ f))
  congr 1

lemma infinitySide_cut_reverse (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    innerHom (completedPureUnit v Ω hΩ (-p))
        (infinitySideHom v Ω hΩ k p false f)=
      infinitySideHom v Ω hΩ k p true ((completedPureAction v _ _).symm f) := by
  rw [show infinitySideHom v Ω hΩ k p false f=
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (mutationSideAction v _ _ false f) from rfl]
  rw [←completed_expand_opposite v Ω hΩ k p hq]
  change PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
    ((completedOppositeInverseAction v _ _).symm
      (mutationSideAction v _ _ false f))=_
  congr 1
  have H:=mutationSideAction_cut_reverse v (complementOmega k Ω) (complementAlpha k p Ω)
    (mutationSideAction v _ _ false f)
  rw [RingEquiv.symm_apply_apply] at H
  exact H.symm
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

lemma mutation_infinity_oriented (pos b : Bool) (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n F.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (G : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc))
    (hG : G.val=mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (orientPowerSeries b F.val)) :
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos
      (rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc) (nonpDegree coord pc) (mutationSize Ω C pc+1)
        (orientPowerSeries b F.val)) = mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit G := by
  let f : CompletedPositive LaurentRay.vUnit Ω C:=⟨orientPowerSeries b F.val,
    orientPowerSeries_constant b F.val F.property.1,orientPowerSeries_graded Ω C b F.val F.property.2⟩
  have hg : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos):=by
    cases b
    · exact inverse_support_addSubmonoid LaurentRay.vUnit Ω _ F.val hf
    · exact hf
  have hb : RegradeBound LaurentRay.vUnit Ω
      (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (mutationSize Ω C pc+1) G.val := by
    rw [hG]
    exact mutationCompletion_nonp_bound LaurentRay.vUnit Ω hΩ C coord hcoord pc pos f hg
  have HT:=congrArg (PowerSeries.map (expandFiberInfinity LaurentRay.vUnit Ω hΩ
      (pureDegree coord pc) (simpleRoot C pc)))
    (mutation_rational_oriented_compatibility Ω hΩ C coord hcoord pc pos b F hf)
  have HG:=congrArg (fun t : PowerSeries (Torus LaurentRay.vUnit Ω) =>
    PowerSeries.map (expandFiberInfinity LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc))
      (rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc) (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
        (mutationSize Ω C pc+1) t)) hG.symm
  exact HT.trans (HG.trans (expandInfinity_rationalRegrade LaurentRay.vUnit Ω hΩ
    (pureDegree coord pc) (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) _ _ _ G.val
    (mutated_series_laurentBounded Ω C coord hcoord pc LaurentRay.vUnit G.property.2) hb))
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

lemma mutation_infinity_oriented_square (pos b : Bool) (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n F.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (hbf : RegradeBound LaurentRay.vUnit Ω (nonpDegree coord pc) (mutationSize Ω C pc+1) F.val)
    (hbi : RegradeBound LaurentRay.vUnit Ω (nonpDegree coord pc) (mutationSize Ω C pc+1) (invOfUnit F.val 1))
    (G : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc))
    (hG : G.val=mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (orientPowerSeries b F.val))
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit G)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos
      (comparisonAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (orientedBounded LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
          (mutationSize Ω C pc+1) (completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc F) hbf hbi b) x) := by
  have hh:=mutation_infinity_oriented Ω hΩ C coord hcoord pc pos b F hf G hG
  cases b
  · exact mapped_unit_square
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos)
      (boundedRationalUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc F)⁻¹ hbi hbf)
      (infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit G) hh x
  · exact mapped_unit_square
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos)
      (boundedRationalUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc F) hbf hbi)
      (infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit G) hh x
end
end ElementaryPositivity.RationalFiber

end

end OAI
