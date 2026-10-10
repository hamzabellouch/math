import OAI.Analysis.IrrationalRotation.Analysis.ChoKoLeeComparison
import OAI.Analysis.IrrationalRotation.Operators.HilbertConjugationExistence

namespace OAI

noncomputable section
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cho_ko_lee_complete_comparison_of_exists
    (hex : ∃ Q : H →L[ℂ] H, Q ≠ 0 ∧ NormQuasinilpotent Q ∧
      HasNoNontrivialHyperinvariantSubspace Q) :
    ∃ Q : H →L[ℂ] H, Q ≠ 0 ∧ NormQuasinilpotent Q ∧
      HasNoNontrivialHyperinvariantSubspace Q ∧
      operatorCommutant (1 + Q) = operatorCommutant Q ∧
      ∀ C : H → H, ∀ hC : IsConjugation C,
        IsInfiniteConjugationIsometry hC.toHilbertConjugation (1 + Q) ∧
        HasNoNontrivialHyperinvariantSubspace (1 + Q) := by
  obtain ⟨Q, hne, hQ, hhyper⟩ := hex
  refine ⟨Q, hne, hQ, hhyper, operatorCommutant_one_add Q, fun C hC => ?_⟩
  exact ⟨isInfiniteConjugationIsometry_one_add_of_isConjugation hC hQ,
    (hasNoNontrivialHyperinvariantSubspace_one_add_iff Q).2 hhyper⟩

theorem exists_conjugation_comparison_of_witness
    {Q : H →L[ℂ] H} (hQ : NormQuasinilpotent Q)
    (hhyper : HasNoNontrivialHyperinvariantSubspace Q) :
    ∃ (C : H → H) (hC : IsConjugation C),
      IsInfiniteConjugationIsometry hC.toHilbertConjugation (1 + Q) ∧
      HasNoNontrivialHyperinvariantSubspace (1 + Q) := by
  obtain ⟨C, hC⟩ := exists_isConjugation (H := H)
  exact ⟨C, hC, isInfiniteConjugationIsometry_one_add_of_isConjugation hC hQ,
    (hasNoNontrivialHyperinvariantSubspace_one_add_iff Q).2 hhyper⟩

end Invariant233

end

end OAI
