import OAI.Algebra.Finitistic.Ordinary.OrdinaryAssociativityNaturality
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFixedTensorFunctor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (k A B N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]

/-- Tensor by the fixed middle bimodule, retaining its actual left action. -/
def middleLeftFunctor : ModuleCat.{u} B ⥤ ModuleCat.{u} A where
  obj Z := ModuleCat.of A (LeftTensor k B A N (BalancedTensor.ScalarLeftModule k B Z))
  map {Z Z'} g := ModuleCat.ofHom
    (LeftTensor.mapLast (k := k) (A := A) (N := N)
      (Z := BalancedTensor.ScalarLeftModule k B Z) (Z' := BalancedTensor.ScalarLeftModule k B Z') g.hom)
  map_id Z := by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro n z
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro n z
    rfl

instance middleLeftFunctor_additive : (middleLeftFunctor k A B N).Additive where
  map_add {Z Z'} {f g} := by
    dsimp only [middleLeftFunctor]
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro n z
    exact (BalancedTensor.mk k B N (BalancedTensor.ScalarLeftModule k B Z') n).map_add (f.hom z) (g.hom z)

/-- Tensor a right module by the middle bimodule, retaining its actual right action. -/
def middleRightFunctor : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{u} Bᵐᵒᵖ where
  obj M := ModuleCat.of Bᵐᵒᵖ (RightTensor k A B (BalancedTensor.ScalarLeftModule k Aᵐᵒᵖ M) N)
  map {M M'} f := ModuleCat.ofHom
    (RightTensor.mapFirst (k := k) (B := B) (N := N)
      (M := BalancedTensor.ScalarLeftModule k Aᵐᵒᵖ M) (M' := BalancedTensor.ScalarLeftModule k Aᵐᵒᵖ M') f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m n
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m n
    rfl

instance middleRightFunctor_additive : (middleRightFunctor k A B N).Additive where
  map_add {M M'} {f g} := by
    dsimp only [middleRightFunctor]
    apply ModuleCat.hom_ext
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro m n
    exact congrArg (fun h => h n)
      ((BalancedTensor.mk k A (BalancedTensor.ScalarLeftModule k Aᵐᵒᵖ M') N).map_add (f.hom m) (g.hom m))

/-- The genuine right tensor complex, with its right B-action. -/
def middleRightComplex (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ) :
    CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ :=
  ((middleRightFunctor k A B N).mapHomologicalComplex (.up ℤ)).obj Q

/-- The genuine left tensor complex, with its left A-action. -/
def middleLeftComplex (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((middleLeftFunctor k A B N).mapHomologicalComplex (.up ℤ)).obj Z
end LittleFinitistic

end

end OAI
