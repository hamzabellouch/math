import OAI.Algebra.Finitistic.Dimension.PDBalancedRight
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

abbrev ScalarModule (M : ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars (algebraMap k A)).obj M

instance scalarModuleTower (M : ModuleCat.{u} A) :
    IsScalarTower k A (ScalarModule k A M) where
  smul_assoc c a m := by
    change (c • a) • (m : M) = algebraMap k A c • (a • (m : M))
    rw [Algebra.smul_def, mul_smul]

variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]

/-- Tensor with a fixed right module, on actual left modules over A. -/
def tensorFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} k where
  obj M := ModuleCat.of k (BalancedTensor.Tensor k A U (ScalarModule k A M))
  map {M N} f := ModuleCat.ofHom
    (mapRight (k := k) (M := ScalarModule k A M) (N := ScalarModule k A N) U f.hom)
  map_id M := by apply ModuleCat.hom_ext; apply BalancedTensor.ext; intros; rfl
  map_comp f g := by apply ModuleCat.hom_ext; apply BalancedTensor.ext; intros; rfl

instance tensorFunctorAdditive : (tensorFunctor k A U).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro u m
    exact map_add (BalancedTensor.mk k A U (ScalarModule k A N) u) (f.hom m) (g.hom m)
end LittleFinitistic.PDTensor

end

end OAI
