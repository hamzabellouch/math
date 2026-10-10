import OAI.Algebra.AuslanderReiten.Duality.FiniteStableResolutionIso
import OAI.Algebra.AuslanderReiten.Fibers.FiniteEvaluatedFiber
import Mathlib.CategoryTheory.Preadditive.Biproducts

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Limits
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
variable {M N : FiniteLeftModule k R}

theorem homotopyResolutionMap_add (f g : M.carrier →ₗ[R] N.carrier) :
    (Q).map (resolutionMap τ (f + g)) = (Q).map (resolutionMap τ f) + (Q).map (resolutionMap τ g) := by
  apply (resolutionHomotopyEquiv τ M N).injective
  rw [map_add, resolutionHomotopyEquiv_map, resolutionHomotopyEquiv_map,
    resolutionHomotopyEquiv_map]
  exact map_add (StableHom.classOf R M.carrier N.carrier) f g

theorem homotopyResolutionMap_zero :
    (Q).map (resolutionMap τ (0 : M.carrier →ₗ[R] N.carrier)) = 0 := by
  apply (resolutionHomotopyEquiv τ M N).injective
  rw [map_zero, resolutionHomotopyEquiv_map]
  exact map_zero (StableHom.classOf R M.carrier N.carrier)

variable (M N)

def pairFst : (pairModule M N).carrier →ₗ[R] M.carrier := LinearMap.fst R _ _
def pairSnd : (pairModule M N).carrier →ₗ[R] N.carrier := LinearMap.snd R _ _
def pairInl : M.carrier →ₗ[R] (pairModule M N).carrier := LinearMap.inl R _ _
def pairInr : N.carrier →ₗ[R] (pairModule M N).carrier := LinearMap.inr R _ _

abbrev resolutionPairBicone : BinaryBicone ((Q).obj (M.completeCochain τ))
    ((Q).obj (N.completeCochain τ)) where
  pt := (Q).obj ((pairModule M N).completeCochain τ)
  fst := (Q).map (resolutionMap (M := pairModule M N) (N := M) τ (pairFst M N))
  snd := (Q).map (resolutionMap (M := pairModule M N) (N := N) τ (pairSnd M N))
  inl := (Q).map (resolutionMap (M := M) (N := pairModule M N) τ (pairInl M N))
  inr := (Q).map (resolutionMap (M := N) (N := pairModule M N) τ (pairInr M N))
  inl_fst := by
    erw [← resolutionMap_comp]
    rw [show (pairFst M N).comp (pairInl M N) = LinearMap.id from by ext x; rfl, resolutionMap_id]
  inl_snd := by
    erw [← resolutionMap_comp]
    rw [show (pairSnd M N).comp (pairInl M N) = 0 from by ext x; rfl, homotopyResolutionMap_zero]
  inr_fst := by
    erw [← resolutionMap_comp]
    rw [show (pairFst M N).comp (pairInr M N) = 0 from by ext x; rfl, homotopyResolutionMap_zero]
  inr_snd := by
    erw [← resolutionMap_comp]
    rw [show (pairSnd M N).comp (pairInr M N) = LinearMap.id from by ext x; rfl, resolutionMap_id]

 theorem resolutionPairBicone_total :
    (resolutionPairBicone τ M N).fst ≫ (resolutionPairBicone τ M N).inl +
      (resolutionPairBicone τ M N).snd ≫ (resolutionPairBicone τ M N).inr =
      𝟙 (resolutionPairBicone τ M N).pt := by
  apply (resolutionHomotopyEquiv τ (pairModule M N) (pairModule M N)).injective
  rw [map_add, resolutionHomotopyEquiv_comp, resolutionHomotopyEquiv_comp,
    resolutionHomotopyEquiv_id]
  simp only [resolutionHomotopyEquiv_map, StableHom.comp_classOf]
  rw [← map_add]
  apply congrArg (StableHom.classOf R _ _)
  ext x
  exact Prod.ext (add_zero _) (zero_add _)

def resolutionPairBilimit : (resolutionPairBicone τ M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (resolutionPairBicone_total τ M N)

instance resolutionPairHasBiproduct : HasBinaryBiproduct ((Q).obj (M.completeCochain τ))
    ((Q).obj (N.completeCochain τ)) :=
  hasBinaryBiproduct_of_total _ (resolutionPairBicone_total τ M N)

def resolutionPairIso : (Q).obj ((pairModule M N).completeCochain τ) ≅
    ((Q).obj (M.completeCochain τ) ⊞ (Q).obj (N.completeCochain τ)) :=
  biprod.uniqueUpToIso _ _ (resolutionPairBilimit τ M N)

@[simp] theorem resolutionPairIso_hom_fst :
    (resolutionPairIso τ M N).hom ≫ biprod.fst =
      (Q).map (resolutionMap (M := pairModule M N) (N := M) τ (pairFst M N)) :=
  by simp [resolutionPairIso]

@[simp] theorem resolutionPairIso_hom_snd :
    (resolutionPairIso τ M N).hom ≫ biprod.snd =
      (Q).map (resolutionMap (M := pairModule M N) (N := N) τ (pairSnd M N)) :=
  by simp [resolutionPairIso]

end ArExplicit.FiniteLeftModule

end

end OAI
