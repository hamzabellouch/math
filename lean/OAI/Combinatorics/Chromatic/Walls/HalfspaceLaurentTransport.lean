import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.BoundedWordLaurent
import OAI.Combinatorics.Chromatic.Walls.CompletedPathIndependence

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

theorem completedTransport_finite_laurent {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (Hside : (0<a (e (simpleRoot C pc)) ∧ 0<b (e (simpleRoot C pc))) ∨
      (a (e (simpleRoot C pc))<0 ∧ b (e (simpleRoot C pc))<0))
    (f : PowerSeries (Torus LaurentRay.vUnit Ω)) (D : ℕ) :
    ∃g : Torus LaurentRay.vUnit Ω,
      coeff D (completedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
        (PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
          (pureDegree_simple_self C coord hcoord pc)) f))=
      embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc) g := by
  obtain ⟨p,hp⟩:=generic_path_avoiding_cut_exists C e a b (e (simpleRoot C pc)) HA HB Hside
  rw [completedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB p]
  exact actualPathAction_finite_laurent Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p hp f D

theorem completedTransport_laurent_lift {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (Hside : (0<a (e (simpleRoot C pc)) ∧ 0<b (e (simpleRoot C pc))) ∨
      (a (e (simpleRoot C pc))<0 ∧ b (e (simpleRoot C pc))<0))
    (f : PowerSeries (Torus LaurentRay.vUnit Ω)) :
    ∃g : PowerSeries (Torus LaurentRay.vUnit Ω),
      completedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
        (PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
          (pureDegree_simple_self C coord hcoord pc)) f)=
      PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc)) g := by
  choose g hg using completedTransport_finite_laurent Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
    HA HB Hside f
  refine ⟨PowerSeries.mk g,?_⟩
  apply PowerSeries.ext
  intro D
  rw [coeff_map,PowerSeries.coeff_mk]
  exact hg D
end
end ElementaryPositivity.RationalFiber

end

end OAI
