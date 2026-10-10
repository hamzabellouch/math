import OAI.Algebra.Finitistic.Bimodule.BimoduleInputNaturality

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {M M' M'' : ModuleCat.{u} (Enveloping k B)}
variable {N N' N'' : ModuleCat.{u} B}

/-- Tensor a bimodule map and an input map, retaining the outside B-action. -/
def tensorAcross (f : M ⟶ M') (g : N ⟶ N') :
    InputTensor k B M N →ₗ[B] InputTensor k B M' N' :=
  ((BimoduleBalancedTensor.functor k B (BalancedTensor.ScalarLeftModule k B N')).map f).hom.comp
    (inputModuleMap k B M g)

@[simp] theorem tensorAcross_mk (f : M ⟶ M') (g : N ⟶ N')
    (m : BimoduleBalancedTensor.Input k B M) (n : BalancedTensor.ScalarLeftModule k B N) :
    tensorAcross f g (BalancedTensor.mk k B _ _ m n) =
      BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B M')
        (BalancedTensor.ScalarLeftModule k B N') (f.hom m) (g.hom n) := rfl

@[simp] theorem tensorAcross_comp (f : M ⟶ M') (f' : M' ⟶ M'')
    (g : N ⟶ N') (g' : N' ⟶ N'') :
    (tensorAcross f' g').comp (tensorAcross f g) = tensorAcross (f ≫ f') (g ≫ g') := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

@[simp] theorem tensorAcross_id :
    tensorAcross (𝟙 M) (𝟙 N) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

@[simp] theorem tensorAcross_zero_left (g : N ⟶ N') :
    tensorAcross (0 : M ⟶ M') g = 0 := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n =>
    exact LinearMap.congr_fun ((BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B M')
      (BalancedTensor.ScalarLeftModule k B N')).map_zero) (g.hom n)
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

@[simp] theorem tensorAcross_zero_right (f : M ⟶ M') :
    tensorAcross f (0 : N ⟶ N') = 0 := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n =>
    exact (BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B M')
      (BalancedTensor.ScalarLeftModule k B N') (f.hom m)).map_zero
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

variable {P : BiComplex k B} {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ}
variable {a b q r : ℤ}

theorem tensorAcross_eq_termMap (f : P.X a ⟶ P.X b) (g : Z.X q ⟶ Z'.X r) :
    tensorAcross f g = termMap f g := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
end LittleFinitistic.BimoduleTotal

end

end OAI
