import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleDerivedTensor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorFunctor

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic
universe u

/-- A finite model for tensoring a genuine bimodule complex, with its support and right projectivity proved. -/
structure FiniteProjectiveBimoduleComplex (k S A : Type u) [Field k] [Ring S] [Ring A]
    [Algebra k S] [Algebra k A] where
  complex : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ
  size : ℕ
  degrees : Fin size → ℤ
  strictMono : StrictMono degrees
  support : ∀ n, n ∉ Set.range degrees → IsZero (complex.X n)
  rightProjective : ∀ n, Module.Projective Aᵐᵒᵖ (BimoduleCoefficients k S A (complex.X n))

namespace FiniteProjectiveBimoduleComplex
variable {k S A : Type u} [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : FiniteProjectiveBimoduleComplex k S A)

instance rightTerm_projective (n : ℤ) : Module.Projective Aᵐᵒᵖ
    (ComplexTensor.rightTerm k A (BimoduleComplexTensor.rightComplex k S A Q.complex) n) := Q.rightProjective n

abbrev tensorFunctor := BimoduleComplexTensor.totalFunctor k S A Q.complex Q.degrees Q.strictMono

/-- The certified model inverts every input quasi-isomorphism; no condition is placed on the input complex. -/
theorem tensorFunctor_quasiIso {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z') [QuasiIso f] :
    QuasiIso (Q.tensorFunctor.map f) :=
  BimoduleComplexTensor.totalFunctor_quasiIso k S A Q.complex Q.degrees Q.strictMono f

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} A)] [HasDerivedCategory.{u+1} (ModuleCat.{u} S)]

def derivedTensor : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  BimoduleComplexTensor.derivedTotal k S A Q.complex Q.degrees Q.strictMono

def comparison : DerivedCategory.Q ⋙ Q.derivedTensor ≅ Q.tensorFunctor ⋙ DerivedCategory.Q :=
  BimoduleComplexTensor.derivedTotalComparison k S A Q.complex Q.degrees Q.strictMono
end FiniteProjectiveBimoduleComplex

/-- A genuine ordinary bimodule supplied with an actual bounded right-projective resolution. -/
structure BoundedBimoduleResolution (k S A : Type u) [Field k] [Ring S] [Ring A]
    [Algebra k S] [Algebra k A] (M : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) extends FiniteProjectiveBimoduleComplex k S A where
  augmentation : complex ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj M
  augmentation_quasiIso : QuasiIso augmentation

namespace BoundedBimoduleResolution
variable {k S A : Type u} [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable {M : ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)} (Q : BoundedBimoduleResolution k S A M)
variable (B N : Type u) [Ring B] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
local instance : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (S ⊗[k] Bᵐᵒᵖ))]

/-- The resolved ordinary tensor object, in the native derived category retaining both outside actions.
The resolution, its quasi-isomorphism, finite support and right projectivity are fields of Q. -/
def tensorOrdinary : DerivedCategory (ModuleCat.{u} (S ⊗[k] Bᵐᵒᵖ)) :=
  DerivedCategory.Q.obj (((bimoduleTensorFunctor k S A Bᵐᵒᵖ N).mapHomologicalComplex (.up ℤ)).obj Q.complex)
end BoundedBimoduleResolution
end LittleFinitistic

end

end OAI
