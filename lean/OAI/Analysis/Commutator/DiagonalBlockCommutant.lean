import Mathlib
import OAI.Analysis.Commutator.BicommutantRange
import OAI.Analysis.Commutator.HilbertBiprodProjections

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

variable (h : Set.centralizer (Set.centralizer (Set.range (diagHom φ ψ)))=Set.range (diagHom φ ψ))

lemma left_mem_diagonal_commutant :
    left (H:=H) (G:=G)∈(BicommutantRange.ofStarHom (H:=Space H G) (diagHom φ ψ) h).commutant := by
  rw [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant]
  rintro _ ⟨a,rfl⟩
  exact left_commutes _ _

lemma right_mem_diagonal_commutant :
    right (H:=H) (G:=G)∈(BicommutantRange.ofStarHom (H:=Space H G) (diagHom φ ψ) h).commutant := by
  rw [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant]
  rintro _ ⟨a,rfl⟩
  exact right_commutes _ _

end Kadison.HilbertBiprod

end

end
end

end OAI
