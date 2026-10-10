import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorInputMaps

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
namespace FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K L : Fin l → CochainComplex (ModuleCat.{u} R) ℤ) (f : ∀ i, K i ⟶ L i)

theorem diagonal_componentMap (n : ℤ) :
    (diagonal L n).comp (componentMap K L f n) = (componentMap K L f (n+1)).comp (diagonal K n) := by
  apply LinearMap.ext
  intro z
  funext i
  exact congrArg (fun g => g.hom (z i)) ((f i).comm n (n+1))

end FiniteColumnComplex
namespace ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable {Z Z' Z'' : CochainComplex (ModuleCat.{u} A) ℤ}
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- Actual tensor total applied to an arbitrary chain map of input complexes. -/
def finiteTotalMap (f : Z ⟶ Z') : finiteTotal k A Q Z p hp ⟶ finiteTotal k A Q Z' p hp :=
  FiniteColumnComplex.complexMap (columns k A Q Z p) (columns k A Q Z' p)
    (FiniteColumnComplex.totalDifferential _ (tensorHorizontal k A Q Z p hp))
    (FiniteColumnComplex.totalDifferential _ (tensorHorizontal k A Q Z' p hp))
    (fun i => columnMap k A Q f (p i)) (by
      intro n
      change (FiniteColumnComplex.diagonal (columns k A Q Z' p) n + matrix k A Q Z' p n).comp _ =
        (FiniteColumnComplex.componentMap _ _ (fun i => columnMap k A Q f (p i)) (n+1)).comp
          (FiniteColumnComplex.diagonal (columns k A Q Z p) n + matrix k A Q Z p n)
      rw [LinearMap.add_comp,LinearMap.comp_add,
        FiniteColumnComplex.diagonal_componentMap,matrix_inputMap])

@[simp] theorem finiteTotalMap_apply (f : Z ⟶ Z') (n : ℤ)
    (z : FiniteColumnComplex.term (columns k A Q Z p) n) (i : Fin l) :
    ((finiteTotalMap k A Q p hp f).f n).hom z i = inputMap k A Q f (p i) (n + -(p i)) (z i) := by
  change ((columnMap k A Q f (p i)).f n).hom (z i) = _
  rw [columnMap_f]
  rfl

@[simp] theorem inputMap_id (p q : ℤ) : inputMap k A Q (𝟙 Z) p q = LinearMap.id := by
  apply BalancedTensor.ext
  intro x y
  rfl

@[simp] theorem inputMap_comp (f : Z ⟶ Z') (g : Z' ⟶ Z'') (p q : ℤ) :
    (inputMap k A Q g p q).comp (inputMap k A Q f p q) = inputMap k A Q (f ≫ g) p q := by
  apply BalancedTensor.ext
  intro x y
  rfl

/-- The actual signed finite tensor total is a functor on all input complexes. -/
def finiteTotalFunctor : CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} k) ℤ where
  obj Z := finiteTotal k A Q Z p hp
  map f := finiteTotalMap k A Q p hp f
  map_id Z := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i
    change ((finiteTotalMap k A Q p hp (𝟙 Z)).f n).hom z i = z i
    erw [finiteTotalMap_apply,inputMap_id,LinearMap.id_apply]
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i
    change ((finiteTotalMap k A Q p hp (f ≫ g)).f n).hom z i =
      ((finiteTotalMap k A Q p hp g).f n).hom (((finiteTotalMap k A Q p hp f).f n).hom z) i
    erw [finiteTotalMap_apply,finiteTotalMap_apply,finiteTotalMap_apply]
    exact (congrArg (fun h => h (z i)) (inputMap_comp k A Q f g (p i) (n + -(p i)))).symm
end ComplexTensor
end LittleFinitistic

end

end OAI
