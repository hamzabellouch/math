import Mathlib
import OAI.Analysis.Commutator.FreeBaseCompression
import OAI.Analysis.Commutator.TracialVectorSubalgebra

namespace OAI

open Lean in
run_cmd modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "double_embedding"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "double_compression_preserves"

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter UniformSpace ContinuousLinearMap

namespace Kadison.TracialSequence

open TracialGNS FreeWordTensor FreeBlocks

def constantSequence {A : Type} [CStarAlgebra A] : A →⋆ₐ[ℂ] (ℕ →ᵇ A) where
  toFun := BoundedContinuousFunction.const ℕ
  map_one' := by ext i; rfl
  map_mul' a b := by ext i; rfl
  map_zero' := by ext i; rfl
  map_add' a b := by ext i; rfl
  commutes' z := by ext i; rfl
  map_star' a := by ext i; rfl

@[simp] lemma constantSequence_apply {A : Type} [CStarAlgebra A] (a : A) :
    constantSequence a=BoundedContinuousFunction.const ℕ a := rfl

lemma trace_constant {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (a : A) :
    sequenceTrace τ ω (leftRestricted τ ω (constantSequence a))=τ a := by
  exact (tendsto_nhds_unique (tendsto_trace τ ω (constantSequence a)) tendsto_const_nhds)

def constantHom {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M) : A →⋆ₐ[ℂ] M :=
  ((leftRestricted τ ω).comp constantSequence).codRestrict M.toStarSubalgebra hconst

@[simp] lemma constantHom_coe {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M) (a : A) :
    (constantHom τ ω M hconst a : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)=
      leftRestricted τ ω (constantSequence a) := rfl

lemma constant_trace {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M) (a : A) :
    τ a=VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) (constantHom τ ω M hconst a) :=
  (trace_constant τ ω a).symm

private abbrev doubleCompressionPreGNS {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (functional : A →ₚ[ℂ] ℂ) :
    SeminormedAddCommGroup functional.PreGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := functional.preGNSpreInnerProdSpace)

lemma double_embedding {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
  (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
  (hone : τ 1=1) (x : τ.GNS) :
    VectorGNS.embedding (subalgebraState τ ω hτ M hM hone).functional
      M.toStarSubalgebra.subtype (sequenceVacuum τ ω)
      (VectorGNS.subalgebraTrace_subtype M (sequenceVacuum τ ω))
      (originalEmbedding τ (subalgebraState τ ω hτ M hM hone)
        (constantHom τ ω M hconst) (constant_trace τ ω M hconst) x)=constantIn τ ω x := by
  let : SeminormedAddCommGroup (subalgebraState τ ω hτ M hM hone).functional.PreGNS :=
    doubleCompressionPreGNS (subalgebraState τ ω hτ M hM hone).functional
  refine (algebraVector_dense τ).induction_on x (isClosed_eq
    ((VectorGNS.embedding (subalgebraState τ ω hτ M hM hone).functional
      M.toStarSubalgebra.subtype (sequenceVacuum τ ω)
      (VectorGNS.subalgebraTrace_subtype M (sequenceVacuum τ ω))).continuous.comp
      (originalEmbedding τ (subalgebraState τ ω hτ M hM hone)
        (constantHom τ ω M hconst) (constant_trace τ ω M hconst)).continuous)
    (constantIn τ ω).continuous) ?_
  intro a
  have ha := originalEmbedding_coe τ (subalgebraState τ ω hτ M hM hone)
    (constantHom τ ω M hconst) (constant_trace τ ω M hconst) a
  refine (congrArg (VectorGNS.embedding (subalgebraState τ ω hτ M hM hone).functional
    M.toStarSubalgebra.subtype (sequenceVacuum τ ω)
    (VectorGNS.subalgebraTrace_subtype M (sequenceVacuum τ ω))) ha).trans ?_
  exact (VectorGNS.embedding_coe (subalgebraState τ ω hτ M hM hone).functional
    M.toStarSubalgebra.subtype (sequenceVacuum τ ω)
    (VectorGNS.subalgebraTrace_subtype M (sequenceVacuum τ ω))
    (constantHom τ ω M hconst a)).trans (by
    change leftRestricted τ ω (constantSequence a) (sequenceVacuum τ ω)=_
    rw [leftRestricted_vacuum]
    apply Subtype.ext
    exact vector_const τ ω a)

lemma double_compression_preserves {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
  (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
  (hone : τ 1=1) (T : τ.GNS →L[ℂ] τ.GNS) (x : τ.GNS) :
    VectorGNS.compression (subalgebraState τ ω hτ M hM hone).functional
      M.toStarSubalgebra.subtype (sequenceVacuum τ ω) (VectorGNS.subalgebraTrace_subtype M (sequenceVacuum τ ω)) (compressed τ ω T)
      (originalEmbedding τ (subalgebraState τ ω hτ M hM hone)
        (constantHom τ ω M hconst) (constant_trace τ ω M hconst) x)=
    originalEmbedding τ (subalgebraState τ ω hτ M hM hone)
        (constantHom τ ω M hconst) (constant_trace τ ω M hconst) (T x) := by
  apply VectorGNS.compression_on_preserved
  calc
    _ = compressed τ ω T (constantIn τ ω x) := congrArg (compressed τ ω T)
      (double_embedding τ ω M hconst hτ hM hone x)
    _ = constantIn τ ω (T x) := compressed_constant τ ω T x
    _ = _ := (double_embedding τ ω M hconst hτ hM hone (T x)).symm

end Kadison.TracialSequence

end

end
end

end OAI
