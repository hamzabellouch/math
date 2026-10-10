import Mathlib
import OAI.Analysis.Commutator.FreeBlockTensor2
import OAI.Analysis.Commutator.HilbertTensors
import OAI.Analysis.Commutator.TensorCompletion

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

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped TensorProduct InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

def dLetters (i : ι) : PreHilbert := ⟨letterSpace t S i⟩

def aLetters (i : ι) : PreHilbert := ⟨factorSpace t S i⟩

@[reducible] def multiplicityTensor (j : ι) : ℕ → Space
  | 0 => ⟨factorSpace t S j⟩
  | n+1 => spaceTensor ⟨letterSpace t S j⟩ (multiplicityTensor j n)

def paramD : ∀ n, BlockParams t S i j n → (Fin n → letterSpace t S i)
  | 0, _ => Fin.elim0
  | n+1, x => Fin.cons x.1.2 (paramD n x.2)

def paramJ : ∀ n, BlockParams t S i j n → multiplicityTensor t S j n
  | 0, z => z
  | n+1, x => x.1.1 ⊗ₜ[ℂ] paramJ n x.2

def blockShuffle : ∀ n, blockTensor t S i j n ≃ₗᵢ[ℂ]
    (PreHilbert.power (dLetters t S i) n ⊗[ℂ] multiplicityTensor t S j n)
  | 0 => (TensorProduct.lidIsometry ℂ (aLetters t S j)).symm
  | n+1 =>
    (TensorProduct.congrIsometry (.refl ℂ (dLetters t S j))
      (TensorProduct.congrIsometry (.refl ℂ (dLetters t S i)) (blockShuffle n))) |>.trans
    (TensorProduct.congrIsometry (.refl ℂ (dLetters t S j))
      (TensorProduct.assocIsometry ℂ (dLetters t S i)
        (PreHilbert.power (dLetters t S i) n) (multiplicityTensor t S j n)).symm) |>.trans
    HilbertCompletion.leftSwap

@[simp] lemma blockShuffle_pure : ∀ n (x : BlockParams t S i j n),
    blockShuffle t S n (blockPure t S n x) =
      PreHilbert.pure (dLetters t S i) n (paramD t S n x) ⊗ₜ[ℂ] paramJ t S n x
  | 0, x => by rfl
  | n+1, x => by
    change HilbertCompletion.leftSwap
      ((TensorProduct.congrIsometry (.refl ℂ (dLetters t S j))
        (TensorProduct.assocIsometry ℂ (dLetters t S i)
          (PreHilbert.power (dLetters t S i) n) (multiplicityTensor t S j n)).symm)
        ((x.1.1 : dLetters t S j) ⊗ₜ[ℂ]
          ((x.1.2 : dLetters t S i) ⊗ₜ[ℂ] blockShuffle t S n (blockPure t S n x.2)))) = _
    rw [blockShuffle_pure n x.2]
    change HilbertCompletion.leftSwap
      ((x.1.1 : dLetters t S j) ⊗ₜ[ℂ]
        (((x.1.2 : dLetters t S i) ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x.2)) ⊗ₜ[ℂ]
          paramJ t S n x.2)) = _
    rw [HilbertCompletion.leftSwap_tmul]
    rfl

def endpointShuffle (n : ℕ) : endpointTensor t S i j n ≃ₗᵢ[ℂ]
    ((aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n) ⊗[ℂ]
      multiplicityTensor t S j n) :=
  (TensorProduct.congrIsometry (.refl ℂ (aLetters t S i)) (blockShuffle t S n)) |>.trans
    (TensorProduct.assocIsometry ℂ (aLetters t S i)
      (PreHilbert.power (dLetters t S i) n) (multiplicityTensor t S j n)).symm

@[simp] lemma endpointShuffle_pure (n : ℕ) (a : factorSpace t S i) (x : BlockParams t S i j n) :
    endpointShuffle t S n (a ⊗ₜ[ℂ] blockPure t S n x) =
      (a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x)) ⊗ₜ[ℂ] paramJ t S n x := by
  change (TensorProduct.assocIsometry ℂ (aLetters t S i)
      (PreHilbert.power (dLetters t S i) n) (multiplicityTensor t S j n)).symm
        ((a : aLetters t S i) ⊗ₜ[ℂ] blockShuffle t S n (blockPure t S n x)) = _
  rw [blockShuffle_pure]
  rfl

abbrev scalarLevel (i : ι) (n : ℕ) := Completion
  (aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n)

abbrev multiplicityLevel (j : ι) (n : ℕ) := Completion (multiplicityTensor t S j n)

def levelShuffle (n : ℕ) : Completion (endpointTensor t S i j n) ≃ₗᵢ[ℂ]
    Completion (scalarLevel t S i n ⊗[ℂ] multiplicityLevel t S j n) :=
  (HilbertCompletion.congr (endpointShuffle t S n)).trans HilbertCompletion.tensor

@[simp] lemma levelShuffle_pure (n : ℕ) (a : aLetters t S i) (x : BlockParams t S i j n) :
    levelShuffle t S n ((HilbertCompletion.coeIsometry (endpointTensor t S i j n)) (a ⊗ₜ[ℂ] blockPure t S n x)) =
      ((((a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x)) : scalarLevel t S i n) ⊗ₜ[ℂ]
        (paramJ t S n x : multiplicityLevel t S j n)) : Completion (scalarLevel t S i n ⊗[ℂ] multiplicityLevel t S j n)) := by
  let y : endpointTensor t S i j n := a ⊗ₜ[ℂ] blockPure t S n x
  change HilbertCompletion.tensor ((HilbertCompletion.congr (endpointShuffle t S n)) (y : Completion (endpointTensor t S i j n))) = _
  rw [HilbertCompletion.congr_coe]
  change HilbertCompletion.tensor ((endpointShuffle t S n (a ⊗ₜ[ℂ] blockPure t S n x)) : Completion ((aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n) ⊗[ℂ] multiplicityTensor t S j n)) = _
  have he : endpointShuffle t S n (a ⊗ₜ[ℂ] blockPure t S n x) =
      (a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x)) ⊗ₜ[ℂ] paramJ t S n x :=
    endpointShuffle_pure t S n (a : factorSpace t S i) x
  exact (congrArg (fun z : (aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n) ⊗[ℂ]
      multiplicityTensor t S j n => HilbertCompletion.tensor
        (E := aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n)
        (F := multiplicityTensor t S j n)
        (z : Completion ((aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n) ⊗[ℂ]
          multiplicityTensor t S j n))) he).trans
    (HilbertCompletion.tensor_coe_tmul
      (E := aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n)
      (F := multiplicityTensor t S j n)
      (a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x)) (paramJ t S n x))

end Kadison.FreeBlocks
end

end OAI
