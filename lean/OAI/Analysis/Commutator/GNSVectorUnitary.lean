import Mathlib
import OAI.Analysis.Commutator.GNSVectorEmbedding

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ)) (hcyc : DenseRange (fun a : A => φ a ξ))

include hcyc in
lemma embedding_surjective : Function.Surjective (embedding τ φ ξ hτ) := by
  have hd : DenseRange (embedding τ φ ξ hτ) := by
    apply hcyc.mono
    rintro y ⟨a,rfl⟩
    exact ⟨TracialGNS.algebraVector τ a,embedding_coe τ φ ξ hτ a⟩
  intro y
  exact (embedding τ φ ξ hτ).isometry.isClosedEmbedding.isClosed_range.closure_subset (hd y)

def equivalence : τ.GNS ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (embedding τ φ ξ hτ) (embedding_surjective τ φ ξ hτ hcyc)

lemma equivalence_algebraVector (a : A) :
    equivalence τ φ ξ hτ hcyc (TracialGNS.algebraVector τ a)=φ a ξ :=
  embedding_coe τ φ ξ hτ a

lemma equivalence_intertwines (a : A) (v : τ.GNS) :
    equivalence τ φ ξ hτ hcyc (τ.gnsStarAlgHom a v)=φ a (equivalence τ φ ξ hτ hcyc v) :=
  congrArg (fun T : τ.GNS →L[ℂ] H => T v) (intertwines τ φ ξ hτ a)

lemma equivalence_conjugates (a : A) :
    (equivalence τ φ ξ hτ hcyc).conjStarAlgEquiv (τ.gnsStarAlgHom a)=φ a := by
  ext v
  change equivalence τ φ ξ hτ hcyc
    (τ.gnsStarAlgHom a ((equivalence τ φ ξ hτ hcyc).symm v))=φ a v
  rw [equivalence_intertwines,LinearIsometryEquiv.apply_symm_apply]

end Kadison.VectorGNS

end

end
end

end OAI
