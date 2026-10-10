import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutatedPureLine

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

lemma mutatedPathProduct_constant {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    constantCoeff (mutatedPathProduct Ω hΩ C coord pc e he L hdeg p N)=1 := by
  induction p with
  | nil=>exact constantCoeff_one
  | append s p ih=>
    simp only [mutatedPathProduct,map_mul,mutatedLineProduct_constant,ih,one_mul]

include hcoord hS hcomp in
lemma mutatedPathProduct_graded {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedPathProduct Ω hΩ C coord pc e he L hdeg p N) := by
  induction p with
  | nil=>exact SeriesGraded.one LaurentRay.vUnit Ω _
  | append s p ih=>
    exact (mutatedLineProduct_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi N).mul LaurentRay.vUnit Ω _ ih

def mutatedPathProductPositive {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  ⟨mutatedPathProduct Ω hΩ C coord pc e he L hdeg p N,
    mutatedPathProduct_constant Ω hΩ C coord pc e he L hdeg p N,
    mutatedPathProduct_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N⟩

def actualInfinityPathProductUnit {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    (PowerSeries (HahnSeries ℤ (Torus LaurentRay.vUnit Ω)))ˣ :=
  infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit
    (mutatedPathProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N)

lemma actualInfinityPathProductUnit_nil (a : Module.Dual ℝ E) (N : ℕ) :
    actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg (.nil a) N=1 :=
  infinityCompletedUnit_one Ω C coord hcoord pc LaurentRay.vUnit _ rfl

lemma actualInfinityPathProductUnit_append {a : Module.Dual ℝ E} (s : GenericLineSegment C e)
    (p : GenericLinePath C e a (s.start C e)) (N : ℕ) :
    actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg (.append s p) N=
      actualInfinityLineProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
        s.direction s.offset s.generic s.lo s.hi N*
      actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N := by
  rw [actualInfinityLineProductUnit_eq]
  exact infinityCompletedUnit_mul Ω C coord hcoord pc LaurentRay.vUnit _ _ _ rfl

lemma actualInfinityPath_product_square {a b : Module.Dual ℝ E}
    (p : GenericLinePath C e a b) (N : ℕ) (hN : 1≤N)
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (decide (0<a (e (simpleRoot C pc)))) x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (decide (0<b (e (simpleRoot C pc))))
      (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N) x) := by
  induction p with
  | nil=>rw [actualInfinityPathProductUnit_nil,innerHom_one]; rfl
  | append s p ih=>
    rw [actualInfinityPathProductUnit_append,innerHom_mul,ih]
    exact (actualInfinityLine_product_square Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi s.ordered (s.start_regular 1) (s.finish_regular 1)
      N hN _).trans (by rw [actualPathWord,comparisonWordAction_append]; rfl)
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

lemma infinitySideHom_coeff_congr (pos : Bool)
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (d : ℕ) (h : coeff d f=coeff d g) :
    coeff d (infinitySideHom v Ω hΩ k p pos f)=coeff d (infinitySideHom v Ω hΩ k p pos g) := by
  cases pos
  · change coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (PowerSeries.map (shearAction v _ _).toRingHom f))=
      coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (PowerSeries.map (shearAction v _ _).toRingHom g))
    simp only [coeff_map,h]
  · change coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) f)=
      coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) g)
    simp only [coeff_map,h]

lemma infinity_embed_X (m : M) :
    expandFiberInfinity v Ω hΩ k p (embed v Ω hΩ k p hp (Torus.X v Ω m))=
      HahnSeries.single (-k m) (Torus.X v Ω m) := by
  classical
  apply HahnSeries.ext
  funext z
  ext n
  rw [expandFiberInfinity_embed_coeff]
  by_cases hm : m=n
  · subst n
    simp only [HahnSeries.coeff_single,Torus.X,Torus.monomial,Finsupp.single_eq_same]
    split <;> simp_all
  · simp only [Torus.X,Torus.monomial,Finsupp.single_eq_of_ne (Ne.symm hm),ite_self,
      HahnSeries.coeff_single]
    split <;> simp_all

def infinityTestInput (pos : Bool) (m : M) :
    PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :=
  (mutationSideAction v (complementOmega k Ω) (complementAlpha k p Ω) pos).symm
    (PowerSeries.C (embed v Ω hΩ k p hp (Torus.X v Ω m)))

lemma infinitySideHom_test (pos : Bool) (m : M) :
    infinitySideHom v Ω hΩ k p pos (infinityTestInput v Ω hΩ k p hp pos m)=
      PowerSeries.C (HahnSeries.single (-k m) (Torus.X v Ω m)) := by
  change PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
    (mutationSideAction v _ _ pos ((mutationSideAction v _ _ pos).symm _))=_
  rw [RingEquiv.apply_symm_apply,PowerSeries.map_C,infinity_embed_X]
end
end ElementaryPositivity.RationalFiber

end

end OAI
