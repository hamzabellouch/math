import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorTotalFunctor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFiniteConeTriangular
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorTotalAcyclic
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
namespace ComplexTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z')

/-- Every shifted projective tensor column preserves arbitrary quasi-isomorphisms. -/
theorem columnMap_quasiIso (p : ℤ) [Module.Projective Aᵐᵒᵖ (rightTerm k A Q p)] [QuasiIso f] :
    QuasiIso (columnMap k A Q f p) := by
  have ht := BalancedTensor.projectiveTensor_quasiIso k A (rightTerm k A Q p) f
  let := ht
  exact inferInstanceAs (QuasiIso ((shiftFunctor _ (-p)).map
    (((BalancedTensor.fixedTensorFunctor k A (rightTerm k A Q p)).mapHomologicalComplex
      (.up ℤ)).map f)))

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The actual signed finite tensor functor preserves quasi-isomorphisms of arbitrary complexes. -/
theorem finiteTotalMap_quasiIso [∀ i, Module.Projective Aᵐᵒᵖ (rightTerm k A Q (p i))] [QuasiIso f] :
    QuasiIso (finiteTotalMap k A Q p hp f) := by
  let (i : Fin l) := columnMap_quasiIso k A Q f (p i)
  unfold finiteTotalMap
  exact FiniteColumnComplex.complexMap_quasiIso _ _ _ _ _ _

end ComplexTensor
namespace OrdinarySimulation.TensorResolution
open scoped TensorProduct
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

def tensorTotalFunctor : CochainComplex (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)) ℤ ⥤
    CochainComplex (ModuleCat.{u} k) ℤ :=
  ComplexTensor.finiteTotalFunctor k (B ⊗[k] ChainAlgebra k l) (integerComplex k B l)
    (finiteDegrees l) (finiteDegrees_strictMono l)

/-- The actual bounded projective Q_T computes a homotopy-invariant tensor on every input complex. -/
theorem tensorTotalFunctor_quasiIso
    {Z Z' : CochainComplex (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)) ℤ} (f : Z ⟶ Z') [QuasiIso f] :
    QuasiIso ((tensorTotalFunctor k B l).map f) :=
  ComplexTensor.finiteTotalMap_quasiIso k (B ⊗[k] ChainAlgebra k l) (integerComplex k B l) f
    (finiteDegrees l) (finiteDegrees_strictMono l)
end OrdinarySimulation.TensorResolution
end LittleFinitistic

end

end OAI
