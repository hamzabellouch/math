import OAI.Algebra.Finitistic.Tensor.BalancedTensorMaps
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u v w z
variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]

abbrev ScalarModule (M : ModuleCat.{w} Aᵐᵒᵖ) :=
  (ModuleCat.restrictScalars (algebraMap k Aᵐᵒᵖ)).obj M

instance scalarModuleTower (M : ModuleCat.{w} Aᵐᵒᵖ) :
    IsScalarTower k Aᵐᵒᵖ (ScalarModule k A M) where
  smul_assoc c a m := by
    change (c • a) • (m : M) = algebraMap k Aᵐᵒᵖ c • (a • (m : M))
    rw [Algebra.smul_def, mul_smul]

variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

/-- The actual tensor evaluation functor on all right A-modules. -/
def tensorFunctor : ModuleCat.{w} Aᵐᵒᵖ ⥤ ModuleCat.{max w z} k where
  obj M := ModuleCat.of k (Tensor k A (ScalarModule k A M) N)
  map {M M'} f := ModuleCat.ofHom
    (mapLeft (k := k) (M := ScalarModule k A M) (M' := ScalarModule k A M') N f.hom)
  map_id M := ModuleCat.hom_ext (mapLeft_id (k := k) N)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    rfl

instance tensorFunctorAdditive : (tensorFunctor k A N).Additive where
  map_add {M M'} {f g} := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    change mk k A (ScalarModule k A M') N (f.hom m + g.hom m) n =
      mk k A (ScalarModule k A M') N (f.hom m) n + mk k A (ScalarModule k A M') N (g.hom m) n
    exact LinearMap.congr_fun ((mk k A (ScalarModule k A M') N).map_add (f.hom m) (g.hom m)) n
end LittleFinitistic.BalancedTensor

end

end OAI
