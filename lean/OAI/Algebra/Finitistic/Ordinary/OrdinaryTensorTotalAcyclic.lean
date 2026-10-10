import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorFiniteMatrix
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorColumnAcyclic
import OAI.Algebra.Finitistic.Ordinary.OrdinaryIntegerResolution

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic
namespace ComplexTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The actual signed finite tensor total of projective right terms preserves acyclicity.
No bound, finiteness, dimension or projectivity condition is imposed on Z. -/
theorem finiteTotal_acyclic [∀ i, Module.Projective Aᵐᵒᵖ (rightTerm k A Q (p i))]
    (hZ : Z.Acyclic) : (finiteTotal k A Q Z p hp).Acyclic :=
  FiniteColumnComplex.total_acyclic (columns k A Q Z p) (tensorHorizontal k A Q Z p hp)
    (fun i => column_acyclic k A Q Z (p i) hZ)

end ComplexTensor
namespace OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

/-- Exactly the manuscript's finite interval [-l,0] of Q_T. -/
def finiteDegrees (i : Fin (l+1)) : ℤ := -(l:ℤ) + i.val

theorem finiteDegrees_strictMono : StrictMono (finiteDegrees l) := by
  intro i j hij
  change -(l:ℤ) + (i.val:ℤ) < -(l:ℤ) + (j.val:ℤ)
  change i.val < j.val at hij
  omega

instance integerTerm_moduleProjective (n : ℤ) :
    Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ
      (ComplexTensor.rightTerm k (B ⊗[k] ChainAlgebra k l) (integerComplex k B l) n) := by
  let := integerTerm_projective k B l n
  exact (inferInstance : Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ ((integerComplex k B l).X n))

/-- Actual signed tensor with the manuscript's Q_T on an arbitrary complex of BC-modules. -/
def tensorTotal (Z : CochainComplex (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)) ℤ) :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  ComplexTensor.finiteTotal k (B ⊗[k] ChainAlgebra k l) (integerComplex k B l) Z
    (finiteDegrees l) (finiteDegrees_strictMono l)

/-- Q_T is K-flat in the acyclic-input characterization, for its actual signed tensor total. -/
theorem tensorTotal_acyclic (Z : CochainComplex (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)) ℤ)
    (hZ : Z.Acyclic) : (tensorTotal k B l Z).Acyclic :=
  ComplexTensor.finiteTotal_acyclic k (B ⊗[k] ChainAlgebra k l) (integerComplex k B l) Z
    (finiteDegrees l) (finiteDegrees_strictMono l) hZ
end OrdinarySimulation.TensorResolution
end LittleFinitistic

end

end OAI
