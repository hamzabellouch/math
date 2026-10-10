import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry11
import OAI.Analysis.Commutator.Regroup
import OAI.Analysis.Commutator.TensorPowerCompletion

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

abbrev factorFull : PreHilbert := ⟨(pullbackState t f hf).functional.GNS⟩

abbrev factorZero : PreHilbert := ⟨HilbertCompletion.centered
  (((pullbackState t f hf).functional.toPreGNS 1 : preSpace (pullbackState t f hf)) :
    (pullbackState t f hf).functional.GNS)⟩

def scalarGNSIso (n : ℕ) : scalarLevel t S i n ≃ₗᵢ[ℂ]
    Completion (factorFull t f hf ⊗[ℂ] PreHilbert.power (factorZero t f hf) n) :=
  HilbertCompletion.wordEquiv (aLetters t S i) (dLetters t S i)
    (factorFull t f hf) (factorZero t f hf)
    ((factorGNSIso t f hf S i hS).trans HilbertCompletion.completeEquiv)
    ((letterGNSIso t f hf S i hS).trans HilbertCompletion.completeEquiv) n

lemma letterGNSIso_pre (x : HilbertCompletion.centered
    ((pullbackState t f hf).functional.toPreGNS 1)) :
    (letterGNSIso t f hf S i hS
      (letterPreMap t f hf S i hS x : Completion (letterSpace t S i)) :
        (pullbackState t f hf).functional.GNS) =
      ((x : preSpace (pullbackState t f hf)) : (pullbackState t f hf).functional.GNS) := by
  change (HilbertCompletion.centeredMap _
    ((HilbertCompletion.congr (letterPreIso t f hf S i hS)).symm
      (letterPreMap t f hf S i hS x : Completion (letterSpace t S i))) :
      (pullbackState t f hf).functional.GNS) = _
  have hx : (letterPreMap t f hf S i hS x : Completion (letterSpace t S i)) =
      HilbertCompletion.congr (letterPreIso t f hf S i hS)
        (x : Completion (HilbertCompletion.centered
          ((pullbackState t f hf).functional.toPreGNS 1))) :=
    (HilbertCompletion.congr_coe (letterPreIso t f hf S i hS) x).symm
  rw [hx, LinearIsometryEquiv.symm_apply_apply, HilbertCompletion.centeredMap_coe]

end Kadison.FreeBlocks
end

end OAI
