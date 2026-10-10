import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorFunctor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorBimoduleResolution
import OAI.Algebra.Finitistic.Ordinary.OrdinarySimulationComparison

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

abbrev genuineTensorFunctor :=
  bimoduleTensorFunctor k B (B ⊗[k] ChainAlgebra k l) Bᵐᵒᵖ (BimoduleO P a l)

def genuineFiniteTermIso (n : ℕ) :
    (genuineTensorFunctor P a l).obj ((TensorResolution.bimoduleComplex k B l).X n) ≅
      (FullTensorTerm.complex P a l).X n := by
  let e : BimoduleCoefficients k B (B ⊗[k] ChainAlgebra k l)
      ((TensorResolution.bimoduleComplex k B l).X n) ≃ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
        TensorResolution.term k B l n := (TensorResolution.forgetBimoduleTerm k B l n).toLinearEquiv
  have he (b : B) (x : BimoduleCoefficients k B (B ⊗[k] ChainAlgebra k l)
      ((TensorResolution.bimoduleComplex k B l).X n)) : e (b • x) = b • e x := by
    apply Subtype.ext
    change TensorIdeal.coefficient b * (x.val * 1) = TensorIdeal.coefficient b * x.val
    rw [mul_one]
  exact (TwoSidedTensor.congrLeft (k := k) (S := B) (T := Bᵐᵒᵖ) (N := BimoduleO P a l) e he).toModuleIso

/-- The actual finite bimodule tensor agrees with the existing full computation, preserving both B-actions. -/
def genuineFiniteComplexIso :
    ((genuineTensorFunctor P a l).mapHomologicalComplex (.up ℕ)).obj
      (TensorResolution.bimoduleComplex k B l) ≅ FullTensorTerm.complex P a l :=
  HomologicalComplex.Hom.isoOfComponents (genuineFiniteTermIso P a l) (by
    intro n m h
    change n+1=m at h
    subst m
    change (genuineFiniteTermIso P a l n).hom ≫ (FullTensorTerm.complex P a l).d n (n+1) =
      (genuineTensorFunctor P a l).map ((TensorResolution.bimoduleComplex k B l).d n (n+1)) ≫
        (genuineFiniteTermIso P a l (n+1)).hom
    have h₁ : (FullTensorTerm.complex P a l).d n (n+1) = ModuleCat.ofHom (FullTensorTerm.differential P a l n) :=
      CochainComplex.of_d (fun n => ModuleCat.of (Enveloping k B) (FullTensorTerm P a l n))
        (fun n => ModuleCat.ofHom (FullTensorTerm.differential P a l n)) n
    have h₂ : (TensorResolution.bimoduleComplex k B l).d n (n+1) =
        ModuleCat.ofHom (TensorResolution.bimoduleDifferential k B l n) :=
      CochainComplex.of_d (fun n => ModuleCat.of (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ)
        (TensorResolution.bimoduleTerm k B l n))
        (fun n => ModuleCat.ofHom (TensorResolution.bimoduleDifferential k B l n)) n
    rw [h₁,h₂]
    apply ModuleCat.hom_ext
    dsimp only [genuineTensorFunctor, bimoduleTensorFunctor, FullTensorTerm.complex]
    apply LinearMap.restrictScalars_injective k
    apply BalancedTensor.ext
    intro q o
    rfl)

/-- The actual all-integer tensor of genuine Q_T with O, retaining both outside B-actions. -/
def genuineComputedTensor : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ :=
  ((genuineTensorFunctor P a l).mapHomologicalComplex (.up ℤ)).obj
    (TensorResolution.integerBimoduleComplex k B l)

/-- Agreement with the preserved full signed-comparison input in every integer degree. -/
def genuineComputedTensorIso : genuineComputedTensor P a l ≅ computedTensorComplex P a l :=
  FunctorExtension.iso (genuineTensorFunctor P a l) (TensorResolution.bimoduleComplex k B l)
      (TensorResolution.degreeEmbedding l) ≪≫
    ((TensorResolution.degreeEmbedding l).extendFunctor _).mapIso (genuineFiniteComplexIso P a l)

/-- The actual ordinary tensor Q_T tensor O is isomorphic to P[b] as B-bimodule complexes.
Only the manuscript support and indexing hypotheses are used. -/
def genuineSourceShiftComparison (b : ℤ) (hb : a+(l:ℤ)=b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) :
    genuineComputedTensor P a l ≅ P⟦b⟧ :=
  genuineComputedTensorIso P a l ≪≫ sourceShiftComparison P a l b hb hP
end LittleFinitistic.OrdinarySimulation

end

end OAI
