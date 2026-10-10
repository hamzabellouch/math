import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalMaps
import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductOpposite

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (L R O T : Type u) [Ring L] [Ring R]
variable [AddCommGroup O] [AddCommGroup T] [Module Lᵐᵒᵖ O] [Module Rᵐᵒᵖ T]
open ProductModules

abbrev inflatedPair : ModuleCat.{u} (Lᵐᵒᵖ × Rᵐᵒᵖ) := ModuleCat.of _
  (((firstInflation Lᵐᵒᵖ Rᵐᵒᵖ).obj (ModuleCat.of Lᵐᵒᵖ O)) ×
    ((secondInflation Lᵐᵒᵖ Rᵐᵒᵖ).obj (ModuleCat.of Rᵐᵒᵖ T)))

attribute [local instance] RingHomInvPair.of_ringEquiv

def rightPairEquiv : OffDiagonal O T ≃ₛₗ[RingHomClass.toRingHom (oppositeEquiv L R)]
    inflatedPair L R O T where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Off-diagonal right projectivity follows from the actual two product-factor modules. -/
theorem right_projective [Module.Projective Lᵐᵒᵖ O] [Module.Projective Rᵐᵒᵖ T] :
    Module.Projective (L × R)ᵐᵒᵖ (OffDiagonal O T) := by
  let P := ModuleCat.of Lᵐᵒᵖ O
  let Q := ModuleCat.of Rᵐᵒᵖ T
  have : Projective P := ModuleCat.projective_of_categoryTheory_projective P
  have : Projective Q := ModuleCat.projective_of_categoryTheory_projective Q
  have : HasProjectiveDimensionLE P 0 := (projective_iff_hasProjectiveDimensionLT_one (X := P)).mp inferInstance
  have : HasProjectiveDimensionLE Q 0 := (projective_iff_hasProjectiveDimensionLT_one (X := Q)).mp inferInstance
  have := firstInflation_dimensionLE Lᵐᵒᵖ Rᵐᵒᵖ 0 P
  have := secondInflation_dimensionLE Lᵐᵒᵖ Rᵐᵒᵖ 0 Q
  let e := ModuleCat.biprodIsoProd ((firstInflation Lᵐᵒᵖ Rᵐᵒᵖ).obj P)
    ((secondInflation Lᵐᵒᵖ Rᵐᵒᵖ).obj Q)
  have : HasProjectiveDimensionLT (inflatedPair L R O T) 1 := hasProjectiveDimensionLT_of_iso e 1
  have : HasProjectiveDimensionLE (ModuleCat.of (L × R)ᵐᵒᵖ (OffDiagonal O T)) 0 :=
    ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv (oppositeEquiv L R).symm
      (rightPairEquiv L R O T).symm 0
  have : Projective (ModuleCat.of (L × R)ᵐᵒᵖ (OffDiagonal O T)) :=
    (projective_iff_hasProjectiveDimensionLT_one (X := ModuleCat.of (L × R)ᵐᵒᵖ (OffDiagonal O T))).mpr inferInstance
  exact ModuleCat.projective_of_module_projective (ModuleCat.of (L × R)ᵐᵒᵖ (OffDiagonal O T))
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI
