import OAI.Algebra.Finitistic.Bar.PatternTensorCoherence

namespace OAI
open CategoryTheory TensorProduct
open scoped TensorProduct
noncomputable section
namespace DerivedBar.Multibar
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (V W : Type u) [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]
  [AddCommGroup W] [Module k W] [Module D W] [IsScalarTower k D W]

/-- The categorical free-bar differential is the supplied-scalars literal one. -/
theorem freeBarObjIso_d (n : ℕ) :
    ((barFunctor k D).obj (ModuleCat.of D V)).d (n+1) n ≫
      (freeBarObjIso k D V n).hom =
    (freeBarObjIso k D V (n+1)).hom ≫
      ModuleCat.ofHom (DerivedBar.differential k D V (n+1)) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  simp only [barFunctor, complex, ChainComplex.of_d]
  rfl

/-- The X-bar differential retains the original noncommutative bimodule actions. -/
theorem twoSidedBarObjIso_d (n : ℕ) :
    ((BimoduleTensor.twoSidedBarFunctor k D X).obj (ModuleCat.of D V)).d (n+1) n ≫
      (twoSidedBarObjIso k D X V n).hom =
    (twoSidedBarObjIso k D X V (n+1)).hom ≫
      ModuleCat.ofHom (BimoduleTensor.barDifferential k D X V n) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  simp only [BimoduleTensor.twoSidedBarFunctor, BimoduleTensor.barComplex, ChainComplex.of_d]
  rfl

/-- Scalar coherence is natural for every D-linear map of input modules. -/
theorem freeBarObjIso_map (f : V →ₗ[D] W) (n : ℕ) :
    ((barFunctor k D).map (ModuleCat.ofHom f)).f n ≫ (freeBarObjIso k D W n).hom =
    (freeBarObjIso k D V n).hom ≫ ModuleCat.ofHom (termMap k D V W f (n+1)) := by
  have hv := BimoduleTensor.scalarModule_eq k D V
  have hw := BimoduleTensor.scalarModule_eq k D W
  cases hv
  cases hw
  rfl

/-- All vertical maps of the categorical X bar become literal tensor maps. -/
theorem twoSidedBarObjIso_map (f : V →ₗ[D] W) (n : ℕ) :
    ((BimoduleTensor.twoSidedBarFunctor k D X).map (ModuleCat.ofHom f)).f n ≫
      (twoSidedBarObjIso k D X W n).hom =
    (twoSidedBarObjIso k D X V n).hom ≫ ModuleCat.ofHom
      (AlgebraTensorModule.lTensor D X ((termMap k D V W f n).restrictScalars k)) := by
  have hv := BimoduleTensor.scalarModule_eq k D V
  have hw := BimoduleTensor.scalarModule_eq k D W
  cases hv
  cases hw
  rfl
end DerivedBar.Multibar

end

end OAI
