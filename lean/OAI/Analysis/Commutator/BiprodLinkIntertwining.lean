import Mathlib
import OAI.Analysis.Commutator.BicommutantRange
import OAI.Analysis.Commutator.BiprodLinkColumn

namespace OAI

noncomputable section

noncomputable section

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

lemma component_diagonal_intertwines
    (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (h : Set.centralizer (Set.centralizer (Set.range (diagHom φ ψ)))=Set.range (diagHom φ ψ))
    (v : Intertwiner (BicommutantRange.ofStarHom (diagHom φ ψ) h).commutant) (a : A) :
    (component _ v).comp (φ a)=(ψ a).comp (component _ v) := by
  apply component_intertwines _ φ ψ v a
  have hm : star v.val ∈ ((BicommutantRange.ofStarHom (diagHom φ ψ) h).commutant : Set _) :=
    (BicommutantRange.ofStarHom (diagHom φ ψ) h).commutant.star_mem' v.mem
  rw [VonNeumannAlgebra.coe_commutant] at hm
  exact hm _ ⟨a,rfl⟩

end Kadison.BiprodLinkColumn
end
end

end OAI
