import Mathlib
import OAI.Analysis.Commutator.FreeWordTensor
import OAI.Analysis.Commutator.GNSVectorEmbedding
import OAI.Analysis.Commutator.NormalGNS
import OAI.Analysis.Commutator.TracialUltrapowerTransfer

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def subalgebraTrace (M : VonNeumannAlgebra H) (ξ : H) : M →ₚ[ℂ] ℂ where
  toLinearMap := (VectorFunctional.functional ξ).toLinearMap.comp M.toStarSubalgebra.subtype.toLinearMap
  monotone' := fun _ _ h => (VectorFunctional.functional ξ).monotone h

@[simp] lemma subalgebraTrace_apply (M : VonNeumannAlgebra H) (ξ : H) (a : M) :
    subalgebraTrace M ξ a=inner ℂ ξ ((a:H →L[ℂ] H) ξ) := rfl

lemma subalgebraTrace_subtype (M : VonNeumannAlgebra H) (ξ : H) (a : M) :
    subalgebraTrace M ξ a=inner ℂ ξ (M.toStarSubalgebra.subtype a ξ) := rfl

lemma subalgebraTrace_normal (M : VonNeumannAlgebra H) (ξ : H) :
    NormalGNS.BoundedWOTContinuous M (subalgebraTrace M ξ) := by
  intro C
  exact (VectorFunctional.continuous_functional_wot ξ).comp continuous_subtype_val

abbrev subalgebraEmbedding (M : VonNeumannAlgebra H) (ξ : H) :
    (subalgebraTrace M ξ).GNS →ₗᵢ[ℂ] H :=
  embedding (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ)

abbrev subalgebraCompression (M : VonNeumannAlgebra H) (ξ : H) (T : H →L[ℂ] H) :
    (subalgebraTrace M ξ).GNS →L[ℂ] (subalgebraTrace M ξ).GNS :=
  compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ
    (subalgebraTrace_subtype M ξ) T

@[simp] lemma subalgebraEmbedding_coe (M : VonNeumannAlgebra H) (ξ : H) (a : M) :
    subalgebraEmbedding M ξ (TracialGNS.algebraVector (subalgebraTrace M ξ) a)=
      (a:H →L[ℂ] H) ξ :=
  embedding_coe (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ
    (subalgebraTrace_subtype M ξ) a

lemma subalgebraCompression_on_preserved (M : VonNeumannAlgebra H) (ξ : H)
    (T : H →L[ℂ] H) (x y : (subalgebraTrace M ξ).GNS)
    (hxy : T (subalgebraEmbedding M ξ x)=subalgebraEmbedding M ξ y) :
    compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ
      (subalgebraTrace_subtype M ξ) T x=y :=
  compression_on_preserved _ _ _ _ T x y hxy

end Kadison.VectorGNS

namespace Kadison.TracialSequence

open TracialGNS FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤Filter.atTop)

variable (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))

include hτ hω hM in
lemma subalgebra_tracial (a b : M) :
    VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) (a*b)=
      VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) (b*a) :=
  bicommutant_trace_mul τ ω hτ hω (hM a) (hM b)

include hτ hM in
lemma subalgebra_faithful (a : M)
    (ha : VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) (star a*a)=0) : a=0 := by
  apply Subtype.ext
  exact trace_faithful τ ω hτ (hM a) ha

lemma subalgebra_normalized (hone : τ 1=1) :
    VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) 1=1 :=
  (trace_one τ ω).trans hone

abbrev subalgebraState (hone : τ 1=1) : FaithfulState M where
  functional := VectorGNS.subalgebraTrace M (sequenceVacuum τ ω)
  normalized := subalgebra_normalized τ ω M hone
  faithful := subalgebra_faithful τ ω hτ M hM

end Kadison.TracialSequence

end

end
end

end OAI
