import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CompletedPathAction

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

theorem actualPathAction_independent {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (p q : GenericLinePath C e a b)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f=
      actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg q f := by
  obtain ⟨r⟩:=generic_path_exists C e b a HB HA
  have H1:=actualPathAction_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
    (p.trans C e r) f
  have H2:=actualPathAction_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
    (r.trans C e q) (actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f)
  rw [actualPathAction_trans] at H1 H2
  rw [H1] at H2
  exact H2.symm

def completedTransport {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) :=
  actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
    (Classical.choice (generic_path_exists C e a b HA HB))

lemma completedTransport_eq_path {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (p : GenericLinePath C e a b)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    completedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB f=
      actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f := by
  exact actualPathAction_independent Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB _ p f

lemma completedTransport_self {a : Module.Dual ℝ E}
    (HA : RegularCovector C e a)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    completedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HA f=f := by
  exact actualPathAction_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg _ f

lemma completedTransport_trans {a b c : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) (HC : RegularCovector C e c)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    completedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HC f=
      completedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HB HC
        (completedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB f) := by
  let p:=Classical.choice (generic_path_exists C e a b HA HB)
  let q:=Classical.choice (generic_path_exists C e b c HB HC)
  rw [completedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HC (p.trans C e q)]
  exact actualPathAction_trans Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p q f
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (u : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
def comparisonWordHom (l : List (ComparisonCrossing u Ω δ k B)) :
    PowerSeries (FiberTorus u (complementOmega k Ω) (complementAlpha k p Ω)) →+*
      PowerSeries (FiberTorus u (complementOmega k Ω) (complementAlpha k p Ω)) :=
  l.foldr (fun c f=>(comparisonAction u Ω hΩ δ k p hp B c).comp f) (RingHom.id _)
lemma comparisonWordHom_apply (l : List (ComparisonCrossing u Ω δ k B))
    (f : PowerSeries (FiberTorus u (complementOmega k Ω) (complementAlpha k p Ω))) :
    comparisonWordHom u Ω hΩ δ k p hp B l f=comparisonWordAction u Ω hΩ δ k p hp B l f := by
  induction l with
  | nil=>rfl
  | cons c l ih=>
    change comparisonAction u Ω hΩ δ k p hp B c (comparisonWordHom u Ω hΩ δ k p hp B l f)=_
    rw [ih]
    rfl
end
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

local instance : AddCommMonoid (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
    (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)) :=
  (FiberTorus.instRing LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
    (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)).toAddCommMonoid

def actualPathHom {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) :
    PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)) →+*
    PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)) where
  toFun:=actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p
  map_one':=by
    apply PowerSeries.ext
    intro D
    rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p 1 D
      (max 1 ((mutationSize Ω C pc+1)*D)) (le_max_left _ _) (le_max_right _ _)]
    rw [←comparisonWordHom_apply,map_one]
  map_zero':=by
    apply PowerSeries.ext
    intro D
    rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p 0 D
      (max 1 ((mutationSize Ω C pc+1)*D)) (le_max_left _ _) (le_max_right _ _)]
    rw [←comparisonWordHom_apply,map_zero]
  map_add':=by
    intro f g
    apply PowerSeries.ext
    intro D
    let A:=max 1 ((mutationSize Ω C pc+1)*D)
    rw [map_add]
    rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p (f+g) D A
      (le_max_left _ _) (le_max_right _ _)]
    rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f D A
      (le_max_left _ _) (le_max_right _ _)]
    rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p g D A
      (le_max_left _ _) (le_max_right _ _)]
    simp only [←comparisonWordHom_apply,map_add]
  map_mul':=by
    intro f g
    apply PowerSeries.ext
    intro D
    let A:=max 1 ((mutationSize Ω C pc+1)*D)
    rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p (f*g) D A
      (le_max_left _ _) (le_max_right _ _)]
    rw [←comparisonWordHom_apply,map_mul]
    simp only [coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hi : ij.1≤D:=by omega
    have hj : ij.2≤D:=by omega
    rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f ij.1 A
      (le_max_left _ _) ((Nat.mul_le_mul_left _ hi).trans (le_max_right _ _))]
    rw [actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p g ij.2 A
      (le_max_left _ _) ((Nat.mul_le_mul_left _ hj).trans (le_max_right _ _))]
    simp only [comparisonWordHom_apply]
end

noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

def completedTransportEquiv {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) :
    PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)) ≃+*
    PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)) where
  toFun:=completedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
  invFun:=completedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HB HA
  left_inv:=by
    intro f
    rw [←completedTransport_trans,completedTransport_self]
  right_inv:=by
    intro f
    rw [←completedTransport_trans,completedTransport_self]
  map_mul':=(actualPathHom Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
    (Classical.choice (generic_path_exists C e a b HA HB))).map_mul
  map_add':=(actualPathHom Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
    (Classical.choice (generic_path_exists C e a b HA HB))).map_add
end
end ElementaryPositivity.RationalFiber

end

end OAI
