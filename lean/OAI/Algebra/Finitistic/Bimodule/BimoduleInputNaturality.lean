import OAI.Algebra.Finitistic.Bimodule.BimoduleInputFunctor
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalTermMaps

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- The canonical maps in the two tensor variables commute, preserving the full outside action. -/
theorem input_tensor_square {M M' : ModuleCat.{u} (Enveloping k B)}
    {N N' : ModuleCat.{u} B} (f : M ⟶ M') (g : N ⟶ N') :
    (inputFunctor k B M).map g ≫
      (BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N')).map f =
    (BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N)).map f ≫
      (inputFunctor k B M').map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => exact (map_zero _).trans (map_zero _).symm
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

variable {P : BiComplex k B} {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ}
variable {a b q r : ℤ}

theorem termMap_decompose (f : P.X a ⟶ P.X b) (g : Z.X q ⟶ Z'.X r) :
    ModuleCat.ofHom (termMap f g) =
      (inputFunctor k B (P.X a)).map g ≫
        (BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z' r)).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => exact (map_zero _).trans (map_zero _).symm
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
end LittleFinitistic.BimoduleTotal

end

end OAI
