import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberHomotopy
import OAI.Algebra.AuslanderReiten.Coordinates.MappedBiproductHom

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "τ" => AFrobeniusTrace k q
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
abbrev simpleHomotopyObject := (Q).obj ((X).completeCochain τ)
local notation "SX" => simpleHomotopyObject q

abbrev SimpleHom (n : ℤ) := SX ⟶ (SX)⟦n⟧
abbrev FiberHom (n : ℤ) := SX ⟶ ((Q).obj ((evaluatedFiber q H₁ H₂).completeCochain τ))⟦n⟧
abbrev MiddleHom (n : ℤ) := SX ⟶ ((Q).obj ((evaluatedMiddle q H₁ H₂).completeCochain τ))⟦n⟧

def middleHomEquiv (n : ℤ) : MiddleHom q H₁ H₂ n ≃ₗ[k]
    (SimpleHom q n × SimpleHom q n) :=
  (Linear.homCongr k (Iso.refl _) ((CategoryTheory.shiftFunctor HC n).mapIso
    (middleProductResolutionIso q H₁ H₂))).trans
      (mappedBiproductHomEquiv k (CategoryTheory.shiftFunctor HC n) SX SX SX)

def fiberHomInclusion (n : ℤ) : FiberHom q H₁ H₂ n →ₗ[k] MiddleHom q H₁ H₂ n :=
  Linear.rightComp k SX ((CategoryTheory.shiftFunctor HC n).map
    ((Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := evaluatedMiddle q H₁ H₂) τ (evaluatedFiberInclusion q H₁ H₂))))

def fiberHomRhoPair (n : ℤ) : FiberHom q H₁ H₂ n →ₗ[k]
    (SimpleHom q n × SimpleHom q n) :=
  (Linear.rightComp k SX ((CategoryTheory.shiftFunctor HC n).map
    ((Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
      (N := X) τ (evaluatedRho₁ q H₁ H₂))))).prod
    (Linear.rightComp k SX ((CategoryTheory.shiftFunctor HC n).map
      ((Q).map (FiniteLeftModule.resolutionMap (M := evaluatedFiber q H₁ H₂)
        (N := X) τ (evaluatedRho₂ q H₁ H₂)))))

theorem middleHomEquiv_inclusion (n : ℤ) (f : FiberHom q H₁ H₂ n) :
    middleHomEquiv q H₁ H₂ n (fiberHomInclusion q H₁ H₂ n f) =
      fiberHomRhoPair q H₁ H₂ n f := by
  apply Prod.ext
  · simp only [middleHomEquiv, LinearEquiv.trans_apply, mappedBiproductHomEquiv_fst,
      Linear.homCongr_apply, Iso.refl_inv, Category.id_comp, Functor.mapIso_hom,
      fiberHomInclusion, Linear.rightComp_apply, fiberHomRhoPair, LinearMap.prod_apply]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [fiberInclusion_product_fst q H₁ H₂]
    rfl
  · simp only [middleHomEquiv, LinearEquiv.trans_apply, mappedBiproductHomEquiv_snd,
      Linear.homCongr_apply, Iso.refl_inv, Category.id_comp, Functor.mapIso_hom,
      fiberHomInclusion, Linear.rightComp_apply, fiberHomRhoPair, LinearMap.prod_apply]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [fiberInclusion_product_snd q H₁ H₂]
    rfl

end ArExplicit.T

end

end OAI
