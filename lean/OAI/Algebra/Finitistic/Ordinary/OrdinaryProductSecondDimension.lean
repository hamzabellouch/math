import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductDimension
import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductSplitting
import Mathlib.Algebra.Category.ModuleCat.Biproducts

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Swapping product factors identifies the two actual inflation constructions. -/
def swapInflationEquiv (P : ModuleCat.{v} R) :
    (firstInflation R L).obj P ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.prodComm : R × L ≃+* L × R)]
      (secondInflation L R).obj P where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Small.{v} L] [Small.{v} R]

theorem secondInflation_dimensionLE (n : ℕ) (P : ModuleCat.{v} R) [HasProjectiveDimensionLE P n] :
    HasProjectiveDimensionLE ((secondInflation L R).obj P) n := by
  have := firstInflation_dimensionLE R L n P
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv
    (RingEquiv.prodComm : R × L ≃+* L × R) (swapInflationEquiv L R P) n

/-- Each module over the product has the same finite bound as its two factors. -/
theorem product_module_bound (n : ℕ)
    (hL : ∀ M : ModuleCat.{v} L, projectiveDimension M ≤ (n : ℕ))
    (hR : ∀ M : ModuleCat.{v} R, projectiveDimension M ≤ (n : ℕ))
    (M : ModuleCat.{v} (L × R)) : projectiveDimension M ≤ (n : ℕ) := by
  have : HasProjectiveDimensionLE (firstObject L R M) n := (projectiveDimension_le_iff _ n).mp (hL _)
  have : HasProjectiveDimensionLE (secondObject L R M) n := (projectiveDimension_le_iff _ n).mp (hR _)
  have := firstInflation_dimensionLE L R n (firstObject L R M)
  have := secondInflation_dimensionLE L R n (secondObject L R M)
  let e := ModuleCat.biprodIsoProd ((firstInflation L R).obj (firstObject L R M))
    ((secondInflation L R).obj (secondObject L R M))
  have : HasProjectiveDimensionLT (pairObject L R M) (n+1) := hasProjectiveDimensionLT_of_iso e (n+1)
  have : HasProjectiveDimensionLT M (n+1) :=
    hasProjectiveDimensionLT_of_iso (splitting L R M).toModuleIso.symm (n+1)
  exact (projectiveDimension_le_iff _ n).mpr inferInstance
end LittleFinitistic.ProductModules

end

end OAI
