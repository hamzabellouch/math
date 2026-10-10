import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationLaurentTransport

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
@[simp] lemma expandInfinity_constant (a : K) :
    expandInfinity (RatFunc.C a)=HahnSeries.C a := by
  change expandZero (reciprocal (RatFunc.C a))=_
  rw [reciprocal_constant,expandZero_constant]
lemma expandInfinity_centeredScalar (n a : ℤ) (b : K) :
    expandInfinity (RatFunc.C b*centeredScalar v n a)=
      HahnSeries.single (-n) (b*(↑(v^(-n*a)):K)) := by
  rw [centeredScalar,←mul_assoc,←map_mul,map_mul,expandInfinity_constant,expandInfinity_X_zpow]
  simp [HahnSeries.C]

def readFiberInfinity (m : M) : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+ K where
  toFun f:=(expandInfinity (f (off k p hp m))).coeff (-k m)*
    (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)
  map_zero':=by simp
  map_add' f g:=by simp [add_mul]
lemma readFiberInfinity_monomial (m n : M) (a : K) :
    readFiberInfinity v Ω k p hp m (embedAdd v Ω k p hp (Torus.monomial v Ω n a))=
      (Torus.monomial v Ω n a) m := by
  classical
  rw [embedAdd_monomial]
  change (expandInfinity ((Finsupp.single (off k p hp n)
    (RatFunc.C a*centeredScalar v (k n) (complementAlpha k p Ω (off k p hp n))))
    (off k p hp m))).coeff (-k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)=Finsupp.single n a m
  by_cases ho : off k p hp n=off k p hp m
  · rw [Finsupp.single_apply,ite_eq_left ho,expandInfinity_centeredScalar]
    by_cases hk : k n=k m
    · have hn : n=m:=split_injective k p hp hk ho
      subst n
      rw [HahnSeries.coeff_single,ite_eq_left rfl,Finsupp.single_eq_same]
      rw [mul_assoc,←Units.val_mul,←zpow_add]
      simp
    · have hn : n≠m:=fun h=>hk (congrArg k h)
      simp [Ne.symm hk,Finsupp.single_eq_of_ne (Ne.symm hn)]
  · have hn : n≠m:=fun h=>ho (congrArg (off k p hp) h)
    rw [Finsupp.single_apply,ite_eq_right ho]
    simp [Finsupp.single_eq_of_ne (Ne.symm hn)]
lemma readFiberInfinity_embedAdd (f : Torus v Ω) (m : M) :
    readFiberInfinity v Ω k p hp m (embedAdd v Ω k p hp f)=f m := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp [map_add,hf,hg]
  | single n a=>exact readFiberInfinity_monomial v Ω k p hp m n a
lemma finite_fiber_zero_infinity (f : Torus v Ω) (m : M) :
    readFiber v Ω k p hp m (embedAdd v Ω k p hp f)=
      readFiberInfinity v Ω k p hp m (embedAdd v Ω k p hp f) := by
  rw [readFiber_embedAdd,readFiberInfinity_embedAdd]
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
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

theorem mutation_rational_compatibility (f : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω) pos
      (rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc) (nonpDegree coord pc) (mutationSize Ω C pc+1) f.val)=
    rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (mutationSize Ω C pc+1)
      (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f.val) := by
  unfold rationalRegrade
  rw [mutationSideAction_embed Ω hΩ C coord hcoord pc]
  change PowerSeries.map _ (PowerSeries.map (mutationTorusPush Ω hΩ C pc pos LaurentRay.vUnit) _)=_
  rw [mutation_regrade_compatibility LaurentRay.vUnit Ω hΩ C coord hcoord pc pos f hf]

theorem mutation_rational_new_coefficient (f : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (d : ℕ) (m : M) :
    readFiberInfinity LaurentRay.vUnit Ω (pureDegree coord pc) (simpleRoot C pc)
      (pureDegree_simple_self C coord hcoord pc) m
      (coeff d (mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
        (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω) pos
        (rationalRegrade LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
          (pureDegree_simple_self C coord hcoord pc) (nonpDegree coord pc) (mutationSize Ω C pc+1) f.val)))=
    coeff d (regrade LaurentRay.vUnit Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
      (mutationSize Ω C pc+1) (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f.val)) m := by
  rw [mutation_rational_compatibility Ω hΩ C coord hcoord pc pos f hf,rationalRegrade,coeff_map]
  exact readFiberInfinity_embedAdd LaurentRay.vUnit Ω _ _ _ _ _
end
end ElementaryPositivity.RationalFiber

end

end OAI
