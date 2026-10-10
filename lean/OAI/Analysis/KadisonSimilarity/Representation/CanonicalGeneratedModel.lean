import OAI.Analysis.KadisonSimilarity.Tracial.TracialL2Closure
import OAI.Analysis.KadisonSimilarity.Representation.GeneratedEmbeddings

namespace OAI

/-! The actual generated algebra for two embedded tracial factors. Its
containment, generation, freeness and matrix tower follow from the concrete
embeddings; there is no separately chosen generated-algebra model. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)

def canonicalGeneratedAlgebra : StarSubalgebra ℂ P :=
  (gnsTracialGeometry τ htr).l2FactorAlgebra φ.range ψ.range

instance canonicalGeneratedAlgebra_isClosed :
    IsClosed (canonicalGeneratedAlgebra τ htr φ ψ : Set P) :=
  inferInstanceAs (IsClosed
    ((gnsTracialGeometry τ htr).l2FactorAlgebra φ.range ψ.range : Set P))

theorem canonicalGenerated_first_mem (a : A) :
    φ a ∈ canonicalGeneratedAlgebra τ htr φ ψ :=
  (gnsTracialGeometry τ htr).left_le_l2FactorAlgebra φ.range ψ.range ⟨a, rfl⟩

theorem canonicalGenerated_second_mem (r : R) :
    ψ r ∈ canonicalGeneratedAlgebra τ htr φ ψ :=
  (gnsTracialGeometry τ htr).right_le_l2FactorAlgebra φ.range ψ.range ⟨r, rfl⟩

def canonicalGeneratedFirst : A →⋆ₐ[ℂ] canonicalGeneratedAlgebra τ htr φ ψ :=
  φ.codRestrict (canonicalGeneratedAlgebra τ htr φ ψ)
    (canonicalGenerated_first_mem τ htr φ ψ)

def canonicalGeneratedSecond : R →⋆ₐ[ℂ] canonicalGeneratedAlgebra τ htr φ ψ :=
  ψ.codRestrict (canonicalGeneratedAlgebra τ htr φ ψ)
    (canonicalGenerated_second_mem τ htr φ ψ)

def canonicalGeneratedTrace :=
  restrictedPositiveTrace τ (canonicalGeneratedAlgebra τ htr φ ψ)

def canonicalGeneratedGeometry :=
  gnsTracialGeometry (canonicalGeneratedTrace τ htr φ ψ)
    (restrictedPositiveTrace_tracial τ (canonicalGeneratedAlgebra τ htr φ ψ) htr)

/-- Generation is a property of the constructed algebra, with the same
factor ranges used by the commutator recovery theorem. -/
theorem canonicalGenerated_generation :
    (canonicalGeneratedGeometry τ htr φ ψ).FactorsTraciallyGenerate
      (canonicalGeneratedFirst τ htr φ ψ).range
      (canonicalGeneratedSecond τ htr φ ψ).range :=
  generatedEmbeddings_factorsTraciallyGenerate τ htr
    (canonicalGeneratedAlgebra τ htr φ ψ) φ ψ
    (canonicalGenerated_first_mem τ htr φ ψ) (canonicalGenerated_second_mem τ htr φ ψ)
    ((gnsTracialGeometry τ htr).l2FactorAlgebra_vector_mem φ.range ψ.range)

theorem canonicalGenerated_freeness (hfree : ScalarFree τ.toLinearMap φ.range ψ.range) :
    ScalarFree (canonicalGeneratedGeometry τ htr φ ψ).trace
      (canonicalGeneratedFirst τ htr φ ψ).range
      (canonicalGeneratedSecond τ htr φ ψ).range :=
  generatedEmbeddings_scalarFree τ htr (canonicalGeneratedAlgebra τ htr φ ψ) φ ψ
    (canonicalGenerated_first_mem τ htr φ ψ) (canonicalGenerated_second_mem τ htr φ ψ) hfree

theorem canonicalGenerated_faithful
    (hf : ∀ a : P, τ (star a * a) = 0 → a = 0) :
    Function.Injective (canonicalGeneratedGeometry τ htr φ ψ).vector :=
  restrictedGNS_vector_injective τ htr (canonicalGeneratedAlgebra τ htr φ ψ) hf

variable [PartialOrder R] [StarOrderedRing R]
  (τR : R →ₚ[ℂ] ℂ) (hψτ : ∀ r, τ (ψ r) = τR r)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

/-- The source matrix tower is transported into this exact generated model. -/
def canonicalGeneratedMatrices
    (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR)) :=
  generatedEmbeddingMatrices τ htr (canonicalGeneratedAlgebra τ htr φ ψ) τR ψ
    (canonicalGenerated_second_mem τ htr φ ψ) hψτ M

def canonicalGeneratedRealSequence (S : RealTracialSequence τR.toLinearMap) :=
  generatedEmbeddingRealSequence τ htr (canonicalGeneratedAlgebra τ htr φ ψ) τR ψ
    (canonicalGenerated_second_mem τ htr φ ψ) hψτ S

end KadisonSimilarity

end

end OAI
