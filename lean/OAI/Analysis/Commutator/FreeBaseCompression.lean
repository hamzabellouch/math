import Mathlib
import OAI.Analysis.Commutator.FreeHilbertEntries
import OAI.Analysis.Commutator.GNSVectorEmbedding
import OAI.Analysis.Commutator.IsometryCompression

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments ContinuousLinearMap

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (τ : B →ₚ[ℂ] ℂ) (t : FaithfulState A) (f : B →⋆ₐ[ℂ] A)
  (htrace : ∀ a,τ a=t.functional (f a))

omit [StarOrderedRing B] in
include htrace in
lemma pullback_vector_trace (a : B) :
    τ a=inner ℂ (TracialGNS.vacuum t.functional)
      ((t.functional.gnsStarAlgHom.comp f) a (TracialGNS.vacuum t.functional)) := by
  change τ a=inner ℂ (TracialGNS.vacuum t.functional)
    (t.functional.gnsStarAlgHom (f a) (TracialGNS.vacuum t.functional))
  rw [TracialGNS.left_vacuum]
  change τ a=inner ℂ (TracialGNS.vacuum t.functional) (TracialGNS.algebraVector t.functional (f a))
  rw [TracialGNS.inner_vacuum_algebraVector]
  exact htrace a

def originalEmbedding : τ.GNS →ₗᵢ[ℂ] t.functional.GNS :=
  VectorGNS.embedding τ (t.functional.gnsStarAlgHom.comp f) (TracialGNS.vacuum t.functional)
    (pullback_vector_trace τ t f htrace)

@[simp] lemma originalEmbedding_coe (a : B) :
    originalEmbedding τ t f htrace (TracialGNS.algebraVector τ a)=
      TracialGNS.algebraVector t.functional (f a) := by
  rw [originalEmbedding,VectorGNS.embedding_coe]
  exact TracialGNS.left_vacuum _ _

variable (R : Bool → StarSubalgebra ℂ A) (hfree : Free R t.functional.toLinearMap)

lemma originalEmbedding_range (hf : ∀ a : B,f a∈R true) :
    Set.range (originalEmbedding τ t f htrace)⊆Set.range (baseEmbedding t R hfree) := by
  rintro _ ⟨x,rfl⟩
  refine (TracialGNS.algebraVector_dense τ).induction_on x
    ((baseEmbedding t R hfree).isometry.isClosedEmbedding.isClosed_range.preimage
      (originalEmbedding τ t f htrace).continuous) ?_
  intro a
  refine ⟨(factorOf t R true (f a) (hf a) : multiplicityLevel t R true 0),?_⟩
  rw [baseEmbedding_factorOf,originalEmbedding_coe]
  rfl

theorem original_commutator_le_base (hf : ∀ a : B,f a∈R true)
    (G : t.functional.GNS →L[ℂ] t.functional.GNS) (T : τ.GNS →L[ℂ] τ.GNS)
    (hGT : ∀ x,G (originalEmbedding τ t f htrace x)=originalEmbedding τ t f htrace (T x))
    (a : B) :
    ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖≤
      ‖FreeCorner.compress (K:=multiplicityLevel t R true 0) (H:=t.functional.GNS) (baseEmbedding t R hfree)
        (G*t.functional.gnsStarAlgHom (f a)-t.functional.gnsStarAlgHom (f a)*G)‖ := by
  have hcomp : VectorGNS.compression τ (t.functional.gnsStarAlgHom.comp f)
      (TracialGNS.vacuum t.functional) (pullback_vector_trace τ t f htrace) G=T := by
    ext x
    exact VectorGNS.compression_on_preserved _ _ _ _ G x (T x) (hGT x)
  rw [←hcomp,VectorGNS.compression_commutator]
  exact @FreeCorner.norm_compress_le_of_range_subset
    t.functional.GNS (multiplicityLevel t R true 0) τ.GNS
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    (originalEmbedding τ t f htrace) (baseEmbedding t R hfree)
    (originalEmbedding_range τ t f htrace R hfree hf) _

end Kadison.FreeBlocks

end

end
end

end OAI
