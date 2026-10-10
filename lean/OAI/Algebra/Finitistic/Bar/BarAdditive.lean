import OAI.Algebra.Finitistic.Bar.TwoSidedBarFunctor

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
variable (V W : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]
  [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]

/-- Each iterated free bar term preserves addition of maps. -/
theorem termMap_add (f g : V →ₗ[D] W) (n : ℕ) :
    termMap k D V W (f+g) n = termMap k D V W f n + termMap k D V W g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro d v
    change d ⊗ₜ[k] termMap k D V W (f+g) n v =
      d ⊗ₜ[k] termMap k D V W f n v + d ⊗ₜ[k] termMap k D V W g n v
    rw [ih, LinearMap.add_apply, TensorProduct.tmul_add]

local instance barAdditiveScalarModule (N : ModuleCat.{u} D) : Module k N :=
  BimoduleTensor.scalarModule k D N
local instance barAdditiveScalarTower (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

instance barFunctor_additive : (barFunctor k D).Additive where
  map_add := by
    intro V W f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact termMap_add k D V W f.hom g.hom (n+1)

namespace BimoduleTensor
variable (X : Type u) [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

instance twoSidedBarFunctor_additive : (twoSidedBarFunctor k D X).Additive where
  map_add := by
    intro V W f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply AlgebraTensorModule.ext
    intro x v
    change x ⊗ₜ[k] termMap k D V W (f.hom+g.hom) n v =
      x ⊗ₜ[k] termMap k D V W f.hom n v + x ⊗ₜ[k] termMap k D V W g.hom n v
    rw [termMap_add, LinearMap.add_apply, TensorProduct.tmul_add]
end BimoduleTensor
end DerivedBar

end

end OAI
