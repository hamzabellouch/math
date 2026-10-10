import OAI.Analysis.KadisonSimilarity.Tracial.MatrixVonNeumannRange
import OAI.Analysis.KadisonSimilarity.Representation.FiniteAmplificationReduction

namespace OAI

/-! A finite diagonal amplification of an actual normal represented algebra
has the expected normal range. -/

noncomputable section
namespace KadisonSimilarity
open scoped CStarAlgebra

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

local instance normalRange_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

theorem amplifiedScalarRepresentation_normal_range
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (M : VonNeumannAlgebra H)
    (hrange : σ.range = M.toStarSubalgebra) (n : ℕ) [NeZero n] :
    (amplifiedScalarRepresentation σ n).range =
      (matrixVonNeumann M.commutant n).commutant.toStarSubalgebra := by
  let ρ := M.commutant.toStarSubalgebra.subtype
  have hρ : (representedMatrixHom ρ n).range =
      (matrixVonNeumann M.commutant n).toStarSubalgebra :=
    representedMatrixHom_range ρ M.commutant (subtype_range_eq M.commutant) n
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    have ha : σ a ∈ M.commutant.commutant := by
      rw [M.commutant_commutant]
      change σ a ∈ M.toStarSubalgebra
      rw [← hrange]
      exact ⟨a, rfl⟩
    have hac : σ a ∈ Set.centralizer (ρ.range : Set (H →L[ℂ] H)) := by
      rintro _ ⟨b, rfl⟩
      exact VonNeumannAlgebra.mem_commutant_iff.mp ha b b.property
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro S hS
    have hSm : S ∈ (representedMatrixHom ρ n).range := by
      rw [hρ]
      exact hS
    obtain ⟨X, rfl⟩ := hSm
    exact amplify_mem_matrixRange_commutant ρ n (σ a) hac _ ⟨X, rfl⟩
  · intro hT
    have hTc : T ∈ Set.centralizer ((representedMatrixHom ρ n).range :
        Set (HilbertCopies H n →L[ℂ] HilbertCopies H n)) := by
      rintro _ ⟨X, rfl⟩
      apply VonNeumannAlgebra.mem_commutant_iff.mp hT
      change representedMatrixHom ρ n X ∈ (matrixVonNeumann M.commutant n).toStarSubalgebra
      rw [← hρ]
      exact ⟨X, rfl⟩
    obtain ⟨B, hTB, hB⟩ := matrixRange_commutant_is_diagonal ρ T hTc
    have hBM : B ∈ M := by
      rw [← M.commutant_commutant]
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro S hS
      exact hB S ⟨⟨S, hS⟩, rfl⟩
    have hBr : B ∈ σ.range := by
      rw [hrange]
      exact hBM
    obtain ⟨a, rfl⟩ := hBr
    exact ⟨a, hTB.symm⟩

end KadisonSimilarity

end

end OAI
