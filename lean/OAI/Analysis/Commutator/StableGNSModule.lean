import Mathlib
import OAI.Analysis.Commutator.CountableGNSColumn
import OAI.Analysis.Commutator.FaithfulVectorGNS
import OAI.Analysis.Commutator.HilbertModuleSchroederBernstein
import OAI.Analysis.Commutator.InfiniteReindex

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.InfiniteAmplification

variable {ι H G : Type*} [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def stableEmbedding (V : H →ₗᵢ[ℂ] Space ι G) : Space ℕ H →ₗᵢ[ℂ] Space ℕ G :=
  letI := Encodable.ofCountable (ℕ×ι)
  (reindex (Encodable.encode' (ℕ×ι))).comp (flatten.comp (mapIsometry V))

omit [CompleteSpace H] [CompleteSpace G] in
lemma stableEmbedding_intertwines (V : H →ₗᵢ[ℂ] Space ι G)
    (S : H →L[ℂ] H) (T : G →L[ℂ] G) (hV : ∀ x i,V (S x) i=T (V x i))
    (x : Space ℕ H) :
    stableEmbedding V (map S x)=map T (stableEmbedding V x) := by
  let := Encodable.ofCountable (ℕ×ι)
  change reindex (Encodable.encode' (ℕ×ι)) (flatten (mapIsometry V (map S x)))=
    map T (reindex (Encodable.encode' (ℕ×ι)) (flatten (mapIsometry V x)))
  rw [←reindex_intertwines]
  congr 1
  ext p
  exact hV (x p.1) p.2

private lemma stable_unitary_of_embeddings {A : Type*} [CStarAlgebra A]
    (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (V : H →ₗᵢ[ℂ] Space ι G) (W : G →ₗᵢ[ℂ] Space ℕ H)
    (hV : ∀ a x i, V (φ a x) i=ψ a (V x i))
    (hW : ∀ a x i, W (ψ a x) i=φ a (W x i)) :
    ∃ U : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ G,
      ∀ a x, U (map (φ a) x)=map (ψ a) (U x) := by
  exact HilbertModuleSB.exists_unitary_of_embeddings
    ((diagonal (ι:=ℕ) (H:=H)).comp φ) ((diagonal (ι:=ℕ) (H:=G)).comp ψ)
    (stableEmbedding V) (stableEmbedding W)
    (fun a x => stableEmbedding_intertwines V (φ a) (ψ a) (hV a) x)
    (fun a x => stableEmbedding_intertwines W (ψ a) (φ a) (hW a) x)

end InfiniteAmplification

namespace NormalRepresentation

open InfiniteAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

private lemma stable_gns_model_of_embedding [TopologicalSpace.SeparableSpace H]
    (τ : M →ₚ[ℂ] ℂ) (hn : NormalGNS.BoundedWOTContinuous M τ)
    (hf : ∀ a, τ (star a*a)=0 → a=0)
    (W : τ.GNS →ₗᵢ[ℂ] Space ℕ H)
    (hW : ∀ (a : M) x i, W (τ.gnsStarAlgHom a x) i=a.val (W x i)) :
    ∃ U : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ τ.GNS,
      ∀ (a : M) x, U (map a.val x)=map (τ.gnsStarAlgHom a) (U x) := by
  have embeddings := exists_countable_gns_embedding (H:=H) M τ hn hf
  obtain ⟨ι,hι,V,hV⟩ := embeddings
  let : Countable ι := hι
  exact stable_unitary_of_embeddings (H:=H) (G:=τ.GNS) (ι:=ι) (A:=M)
    M.subtype τ.gnsStarAlgHom V W hV hW

theorem exists_stable_gns_model [TopologicalSpace.SeparableSpace H] :
    ∃ τ : M →ₚ[ℂ] ℂ, NormalGNS.BoundedWOTContinuous M τ ∧
      (∀ a,τ (star a*a)=0 → a=0) ∧
      ∃ U : Space ℕ H ≃ₗᵢ[ℂ] Space ℕ τ.GNS,
        ∀ (a : M) x,U (map (a : H →L[ℂ] H) x)=map (τ.gnsStarAlgHom a) (U x) := by
  let x : ℕ → H := TopologicalSpace.denseSeq H
  have hx : DenseRange x := TopologicalSpace.denseRange_denseSeq H
  let τ := FaithfulNormalFunctional.restricted x M
  have hn := FaithfulNormalFunctional.restricted_normal x M
  have hf := FaithfulNormalFunctional.restricted_faithful x M hx
  refine ⟨τ,hn,hf,?_⟩
  exact stable_gns_model_of_embedding M τ hn hf
    (FaithfulNormalFunctional.gnsEmbedding x M)
    (FaithfulNormalFunctional.gnsEmbedding_intertwines x M)

end NormalRepresentation

end Kadison

end

end
end

end OAI
