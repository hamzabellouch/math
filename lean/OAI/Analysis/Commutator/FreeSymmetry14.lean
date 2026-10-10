import Mathlib
import OAI.Analysis.Commutator.EndpointGNS
import OAI.Analysis.Commutator.FreeBlockTensor4
import OAI.Analysis.Commutator.FreeSymmetry13
import OAI.Analysis.Commutator.TensorMultiplicity

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

open FreeWordTensor UniformSpace PreHilbert

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

abbrev factorTrace := (pullbackState t f hf).functional

abbrev sourceScalar (n : ℕ) := PreHilbert.wordSpace
  (factorFull t f hf) (factorZero t f hf) n

abbrev sourceLevel (n : ℕ) := Completion (sourceScalar t f hf n ⊗[ℂ] multiplicityLevel t S j n)

lemma scalarGNSIso_pure (n : ℕ) (a : aLetters t S i) (x : Fin n → dLetters t S i) :
    scalarGNSIso t f hf S i hS n
      ((a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n x) : scalarLevel t S i n) =
      PreHilbert.word (factorFull t f hf) (factorZero t f hf) n
        (factorGNSIso t f hf S i hS (HilbertCompletion.coeIsometry (aLetters t S i) a))
        (fun k => letterGNSIso t f hf S i hS (HilbertCompletion.coeIsometry (dLetters t S i) (x k))) := by
  have result := HilbertCompletion.wordEquiv_pure (aLetters t S i) (dLetters t S i)
    (factorFull t f hf) (factorZero t f hf)
    ((factorGNSIso t f hf S i hS).trans HilbertCompletion.completeEquiv)
    ((letterGNSIso t f hf S i hS).trans HilbertCompletion.completeEquiv)
    n a (factorGNSIso t f hf S i hS (HilbertCompletion.coeIsometry (aLetters t S i) a))
    rfl x (fun index => letterGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (dLetters t S i) (x index))) (fun _ => rfl)
  dsimp only [scalarGNSIso, PreHilbert.word, factorFull, factorZero,
    TracialGNS.fullSpace, TracialGNS.zeroSpace, TracialGNS.vacuum, factorTrace,
    HilbertCompletion.centered, centeredSpace] at result ⊢
  exact result

def sourceLevelShuffle (n : ℕ) : Completion (endpointTensor t S i j n) ≃ₗᵢ[ℂ]
    sourceLevel t f hf S j n :=
  (levelShuffle t S n).trans (HilbertCompletion.congr
    (TensorProduct.congrIsometry (scalarGNSIso t f hf S i hS n)
      (.refl ℂ (multiplicityLevel t S j n))))

lemma sourceLevelShuffle_word (n : ℕ) (a : aLetters t S i) (x : BlockParams t S i j n) :
    sourceLevelShuffle t f hf S i j hS n
      (HilbertCompletion.coeIsometry (endpointTensor t S i j n) (a ⊗ₜ[ℂ] blockPure t S n x)) =
      HilbertTensor.pair (E := sourceScalar t f hf n) (scalarGNSIso t f hf S i hS n
        ((a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x)) : scalarLevel t S i n))
        (paramJ t S n x : multiplicityLevel t S j n) := by
  change HilbertCompletion.congr _ (levelShuffle t S n
    (HilbertCompletion.coeIsometry (endpointTensor t S i j n) (a ⊗ₜ[ℂ] blockPure t S n x))) = _
  rw [levelShuffle_pure t S n a x, HilbertCompletion.congr_coe]
  rfl

lemma sourceLevelShuffle_pure (n : ℕ) (a : aLetters t S i) (x : BlockParams t S i j n) :
    sourceLevelShuffle t f hf S i j hS n
      (HilbertCompletion.coeIsometry (endpointTensor t S i j n) (a ⊗ₜ[ℂ] blockPure t S n x)) =
      HilbertTensor.pair (E := sourceScalar t f hf n)
        (PreHilbert.word (factorFull t f hf) (factorZero t f hf) n
          (factorGNSIso t f hf S i hS (HilbertCompletion.coeIsometry (aLetters t S i) a))
          (fun k => letterGNSIso t f hf S i hS
            (HilbertCompletion.coeIsometry (dLetters t S i) (paramD t S n x k))))
        (paramJ t S n x : multiplicityLevel t S j n) := by
  rw [sourceLevelShuffle_word]
  exact congrArg (fun b : sourceScalar t f hf n =>
    HilbertTensor.pair b (paramJ t S n x : multiplicityLevel t S j n))
    (scalarGNSIso_pure t f hf S i hS n a (fun k => (paramD t S n x k : dLetters t S i)))

variable (hfree : FreeMoments.Free S t.functional.toLinearMap) (hij : i≠j)

def sourceLevelEmbedding (n : ℕ) : sourceLevel t f hf S j n →ₗᵢ[ℂ] t.functional.GNS :=
  (levelEmbedding t S hfree hij n).comp
    (sourceLevelShuffle t f hf S i j hS n).symm.toLinearIsometry

lemma sourceLevelEmbedding_shuffle (n : ℕ) (x : Completion (endpointTensor t S i j n)) :
    sourceLevelEmbedding t f hf S i j hS hfree hij n
      (sourceLevelShuffle t f hf S i j hS n x) = levelEmbedding t S hfree hij n x := by
  simp [sourceLevelEmbedding]

lemma sourceLevelEmbedding_range (n : ℕ) :
    LinearMap.range (sourceLevelEmbedding t f hf S i j hS hfree hij n).toLinearMap =
      LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨(sourceLevelShuffle t f hf S i j hS n).symm x,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨sourceLevelShuffle t f hf S i j hS n x,
      sourceLevelEmbedding_shuffle t f hf S i j hS hfree hij n x⟩

lemma sourceLevelEmbedding_orthogonal :
    OrthogonalFamily ℂ (fun n => sourceLevel t f hf S j n)
      (sourceLevelEmbedding t f hf S i j hS hfree hij) := by
  intro n m hnm x y
  exact levelEmbedding_orthogonal t S hfree hij hnm
    ((sourceLevelShuffle t f hf S i j hS n).symm x)
    ((sourceLevelShuffle t f hf S i j hS m).symm y)

variable (hcolors : ∀ c : ι, c=i ∨ c=j)

variable (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

include hcolors hgen in
lemma sourceLevelIsHilbertSum : IsHilbertSum ℂ (sourceLevel t f hf S j)
    (sourceLevelEmbedding t f hf S i j hS hfree hij) := by
  apply IsHilbertSum.mk (sourceLevelEmbedding_orthogonal t f hf S i j hS hfree hij)
  have hr : (⨆ n, LinearMap.range (sourceLevelEmbedding t f hf S i j hS hfree hij n).toLinearMap) =
      ⨆ n, LinearMap.range (levelEmbedding t S hfree hij n).toLinearMap := by
    congr 1
    funext n
    exact sourceLevelEmbedding_range t f hf S i j hS hfree hij n
  rw [hr]
  exact le_of_eq (total_levels t S hfree hij hcolors hgen).symm

end Kadison.FreeBlocks
end

end OAI
