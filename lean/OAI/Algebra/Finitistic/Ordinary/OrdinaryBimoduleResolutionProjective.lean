import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorBimoduleResolution
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTensorTerms
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorTotalAcyclic

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

/-- The actual genuine bimodule resolution is right-projective in every integer degree. -/
instance integerBimoduleRight_projective (n : ℤ) :
    Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ
      (ComplexTensor.rightTerm k (B ⊗[k] ChainAlgebra k l)
        (BimoduleComplexTensor.rightComplex k B (B ⊗[k] ChainAlgebra k l) (integerBimoduleComplex k B l)) n) := by
  let e := (HomologicalComplex.eval _ _ n).mapIso (forgetIntegerBimoduleComplex k B l)
  let : Projective ((((forgetBimodule k B l).mapHomologicalComplex (.up ℤ)).obj
      (integerBimoduleComplex k B l)).X n) := Projective.of_iso e.symm (integerTerm_projective k B l n)
  exact ModuleCat.projective_of_module_projective
    ((((forgetBimodule k B l).mapHomologicalComplex (.up ℤ)).obj (integerBimoduleComplex k B l)).X n)

theorem integerBimodule_lower (n : ℤ) (hn : n < -(l:ℤ)) : IsZero ((integerBimoduleComplex k B l).X n) := by
  apply (bimoduleComplex k B l).isZero_extend_X (degreeEmbedding l) n
  intro j hj
  simp only [degreeEmbedding_apply] at hj
  omega

theorem integerBimodule_upper (n : ℤ) (hn : 0 < n) : IsZero ((integerBimoduleComplex k B l).X n) := by
  have h := (integerTerm_upper k B l n hn).of_iso
    ((HomologicalComplex.eval _ _ n).mapIso (forgetIntegerBimoduleComplex k B l))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hs := ModuleCat.isZero_iff_subsingleton.mp h
  exact hs
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
