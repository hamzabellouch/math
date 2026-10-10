import OAI.Algebra.Finitistic.Bar.DerivedCountShift
import OAI.Algebra.Finitistic.Bar.DirectSumCoproduct
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
open Multibar.Indexed
local instance countProjectiveShapeDecidableEq (n r : ℕ) : DecidableEq (Shape n r) :=
  Classical.decEq _

instance outerTensor_free {n r : ℕ} (p : Shape n r) :
    Module.Free D (outerTensor k D X N p) :=
  Module.Free.of_basis (Algebra.TensorProduct.basis D
    (Module.Free.chooseBasis k (tensor k D X N p)))

instance countWeight_free (n r : ℕ) :
    Module.Free D (SquareZero.twoSidedWeight k D X N n r) :=
  Module.Free.of_equiv (decomposition k D X N n r)

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
  (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)

instance countComplex_projective (r n : ℕ) :
    Projective ((SquareZero.twoSidedWeightComplex k D X N hN r).X n) := by
  change Projective (ModuleCat.of D (SquareZero.twoSidedWeight k D X N n r))
  infer_instance

instance countSum_projective (n : ℕ) :
    Projective ((directSumComplex (SquareZero.twoSidedWeightComplex k D X N hN)).X n) := by
  classical
  let (r : ℕ) : Module.Free D ((SquareZero.twoSidedWeightComplex k D X N hN r).X n) :=
    countWeight_free k D X N n r
  change Projective (ModuleCat.of D (⨁ r : ℕ, (SquareZero.twoSidedWeightComplex k D X N hN r).X n))
  infer_instance

instance integerCount_isKProjective (r : ℕ) :
    ((integerExtension D).obj (SquareZero.twoSidedWeightComplex k D X N hN r)).IsKProjective := by
  change CochainComplex.IsKProjective ((SquareZero.twoSidedWeightComplex k D X N hN r).extend
    ComplexShape.embeddingDownNat)
  infer_instance

instance integerCountSum_isKProjective :
    ((integerExtension D).obj (directSumComplex
      (SquareZero.twoSidedWeightComplex k D X N hN))).IsKProjective := by
  change CochainComplex.IsKProjective ((directSumComplex (SquareZero.twoSidedWeightComplex k D X N hN)).extend
    ComplexShape.embeddingDownNat)
  infer_instance
end DerivedBar

end

end OAI
