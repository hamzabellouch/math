import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry14
import OAI.Analysis.Commutator.FreeSymmetry6
import OAI.Analysis.Commutator.TensorMultiplicity2

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
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace PreHilbert

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

def factorBounded (d : D) : factorSpace t S i :=
  factorPreMap t f hf S i hS ((pullbackState t f hf).functional.toPreGNS d)

lemma factorBounded_surjective : Function.Surjective (factorBounded t f hf S i hS) := by
  intro a
  obtain ⟨v,hv⟩ := factorPreMap_surjective t f hf S i hS a
  refine ⟨(pullbackState t f hf).functional.ofPreGNS v,?_⟩
  simpa only [factorBounded,PositiveLinearMap.toPreGNS_ofPreGNS] using hv

@[simp] lemma factorBounded_value (d : D) :
    factorValue t S i (factorBounded t f hf S i hS d)=f d := rfl

@[simp] lemma factorBounded_GNS (d : D) :
    factorGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (aLetters t S i) (factorBounded t f hf S i hS d)) =
      TracialGNS.algebraVector (factorTrace t f hf) d := by
  exact factorGNSIso_coe t f hf S i hS d

def levelWord (d : D) (n : ℕ) (x : BlockParams t S i j n) : sourceLevel t f hf S j n :=
  HilbertTensor.pair (E := sourceScalar t f hf n) (J := multiplicityLevel t S j n)
    (by
      exact PreHilbert.word (factorFull t f hf)
        (factorZero t f hf) n
        (TracialGNS.algebraVector (factorTrace t f hf) d)
        (fun k => letterGNSIso t f hf S i hS
          (HilbertCompletion.coeIsometry (dLetters t S i) (paramD t S n x k))))
    (paramJ t S n x : multiplicityLevel t S j n)

lemma sourceLevelShuffle_bounded (d : D) (n : ℕ) (x : BlockParams t S i j n) :
    sourceLevelShuffle t f hf S i j hS n
      (HilbertCompletion.coeIsometry (endpointTensor t S i j n)
        (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x)) =
      levelWord t f hf S i j hS d n x := by
  have result := sourceLevelShuffle_pure t f hf S i j hS n (factorBounded t f hf S i hS d) x
  rw [factorBounded_GNS] at result
  dsimp only [levelWord, sourceScalar, factorFull, factorZero, TracialGNS.fullSpace,
    TracialGNS.zeroSpace, TracialGNS.vacuum, factorTrace, HilbertCompletion.centered,
    centeredSpace] at result ⊢
  exact result

def endpointCoordinate (n : ℕ) : endpointTensor t S i j n →ₗ[ℂ] sourceLevel t f hf S j n :=
  (sourceLevelShuffle t f hf S i j hS n).toLinearMap.comp
    (HilbertCompletion.coeIsometry (endpointTensor t S i j n)).toLinearMap

lemma endpointCoordinate_pure (d : D) (n : ℕ) (x : BlockParams t S i j n) :
    endpointCoordinate t f hf S i j hS n
      (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x) =
      levelWord t f hf S i j hS d n x :=
  sourceLevelShuffle_bounded t f hf S i j hS d n x

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma sourceLevel_ext (n : ℕ) (F G : sourceLevel t f hf S j n →L[ℂ] E)
    (h : ∀ d x, F (levelWord t f hf S i j hS d n x)=G (levelWord t f hf S i j hS d n x)) :
    F=G := by
  ext v
  obtain ⟨v,rfl⟩ := (sourceLevelShuffle t f hf S i j hS n).surjective v
  change F (sourceLevelShuffle t f hf S i j hS n v)=G (sourceLevelShuffle t f hf S i j hS n v)
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
    change F (endpointCoordinate t f hf S i j hS n v)=G (endpointCoordinate t f hf S i j hS n v)
    induction v using endpointTensor_induction_on t S n with
    | h0 => simp
    | ha v w hv hw => simpa only [map_add] using congrArg₂ (·+·) hv hw
    | ht a b =>
      obtain ⟨d,rfl⟩ := factorBounded_surjective t f hf S i hS a
      let Q : blockTensor t S i j n →ₗ[ℂ] endpointTensor t S i j n :=
        TensorProduct.mk ℂ (factorSpace t S i) (blockTensor t S i j n)
          (factorBounded t f hf S i hS d)
      let K : blockTensor t S i j n →ₗ[ℂ] E :=
        ((F.toLinearMap-G.toLinearMap).comp (endpointCoordinate t f hf S i j hS n)).comp Q
      have hker : Submodule.span ℂ (Set.range (blockPure t S (i:=i) (j:=j) n)) ≤ K.ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨x,rfl⟩
        change F (endpointCoordinate t f hf S i j hS n
          (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x)) -
          G (endpointCoordinate t f hf S i j hS n
            (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x))=0
        exact sub_eq_zero.mpr ((congrArg F (endpointCoordinate_pure t f hf S i j hS d n x)).trans
          ((h d x).trans (congrArg G (endpointCoordinate_pure t f hf S i j hS d n x)).symm))
      have hb : b∈Submodule.span ℂ (Set.range (blockPure t S (i:=i) (j:=j) n)) := by
        rw [span_blockPure]; trivial
      exact sub_eq_zero.mp (hker hb)

variable (hfree : FreeMoments.Free S t.functional.toLinearMap) (hij : i≠j)

lemma sourceLevelEmbedding_word (d : D) (n : ℕ) (x : BlockParams t S i j n) :
    sourceLevelEmbedding t f hf S i j hS hfree hij n (levelWord t f hf S i j hS d n x) =
      t.functional.gnsStarAlgHom (f d)
        (blockReadPre t S n (blockPure t S n x) : t.functional.GNS) := by
  rw [←sourceLevelShuffle_bounded,sourceLevelEmbedding_shuffle]
  exact (levelEmbedding_coe t S hfree hij n
    (factorBounded t f hf S i hS d ⊗ₜ[ℂ] blockPure t S n x)).trans
      (endpointRead_tmul t S n (factorBounded t f hf S i hS d) (blockPure t S n x))

def sourceLeft (a : D) (n : ℕ) : sourceLevel t f hf S j n →L[ℂ] sourceLevel t f hf S j n :=
  HilbertTensor.map
    (HilbertTensor.map ((factorTrace t f hf).gnsStarAlgHom a)
      (1 : power (factorZero t f hf) n →L[ℂ] power (factorZero t f hf) n))
    (1 : multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

lemma sourceLeft_word (a d : D) (n : ℕ) (x : BlockParams t S i j n) :
    sourceLeft t f hf S j a n (levelWord t f hf S i j hS d n x)=
      levelWord t f hf S i j hS (a*d) n x := by
  simp only [sourceLeft, levelWord, PreHilbert.word, HilbertTensor.map_pair,
    HilbertTensor.map_coe_tmul, one_apply_eq_self, TracialGNS.algebraVector_apply,
    TracialGNS.left_coe]

lemma sourceLevelEmbedding_left (a : D) (n : ℕ) :
    (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap.comp
        (sourceLeft t f hf S j a n) =
      (t.functional.gnsStarAlgHom (f a)).comp
        (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap := by
  apply sourceLevel_ext t f hf S i j hS
  intro d x
  simp only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    sourceLeft_word,sourceLevelEmbedding_word,map_mul]
  rfl

end Kadison.FreeBlocks
end

end OAI
