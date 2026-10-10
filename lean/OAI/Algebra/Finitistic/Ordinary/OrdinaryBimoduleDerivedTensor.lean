import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTotalFunctor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleResolutionProjective
import Mathlib.Algebra.Homology.DerivedCategory.Basic

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} S)]
variable [∀ i, Module.Projective Aᵐᵒᵖ (ComplexTensor.rightTerm k A (rightComplex k S A Q) (p i))]

omit [HasDerivedCategory.{u+1} (ModuleCat.{u} A)] in
theorem total_inverts : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).IsInvertedBy
    (totalFunctor k S A Q p hp ⋙ DerivedCategory.Q) := by
  intro Z Z' f hf
  let : QuasiIso f := hf
  let := totalFunctor_quasiIso k S A Q p hp f
  exact (inferInstance : IsIso (DerivedCategory.Q.map ((totalFunctor k S A Q p hp).map f)))

/-- Localization of the actual tensor total, retaining the outside action. -/
def derivedTotal : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  Localization.lift (totalFunctor k S A Q p hp ⋙ DerivedCategory.Q)
    (total_inverts k S A Q p hp) DerivedCategory.Q

def derivedTotalComparison :
    DerivedCategory.Q ⋙ derivedTotal k S A Q p hp ≅ totalFunctor k S A Q p hp ⋙ DerivedCategory.Q :=
  Localization.fac (totalFunctor k S A Q p hp ⋙ DerivedCategory.Q)
    (total_inverts k S A Q p hp) DerivedCategory.Q
end LittleFinitistic.BimoduleComplexTensor
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l))]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- The actual Q_T tensor lift with the source's left B-action retained. -/
def derivedBimoduleTensor : DerivedCategory (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)) ⥤
    DerivedCategory (ModuleCat.{u} B) :=
  BimoduleComplexTensor.derivedTotal k B (B ⊗[k] ChainAlgebra k l) (integerBimoduleComplex k B l)
    (finiteDegrees l) (finiteDegrees_strictMono l)

def derivedBimoduleTensorComparison :
    DerivedCategory.Q ⋙ derivedBimoduleTensor k B l ≅
      BimoduleComplexTensor.totalFunctor k B (B ⊗[k] ChainAlgebra k l) (integerBimoduleComplex k B l)
        (finiteDegrees l) (finiteDegrees_strictMono l) ⋙ DerivedCategory.Q :=
  BimoduleComplexTensor.derivedTotalComparison k B (B ⊗[k] ChainAlgebra k l) (integerBimoduleComplex k B l)
    (finiteDegrees l) (finiteDegrees_strictMono l)
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
