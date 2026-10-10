import OAI.Analysis.IrrationalRotation.Operators.ConjugationDefect
import OAI.Analysis.IrrationalRotation.Operators.CommutantAlgebra

namespace OAI

noncomputable section
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cho_ko_lee_comparison_of_witness (Q : H →L[ℂ] H)
    (hne : Q ≠ 0) (hQ : NormQuasinilpotent Q)
    (hhyper : HasNoNontrivialHyperinvariantSubspace Q) :
    Q ≠ 0 ∧ NormQuasinilpotent Q ∧
      ∀ C : HilbertConjugation H,
        IsInfiniteConjugationIsometry C (1 + Q) ∧
        operatorCommutant (1 + Q) = operatorCommutant Q ∧
        HasNoNontrivialHyperinvariantSubspace (1 + Q) := by
  refine ⟨hne, hQ, fun C => ?_⟩
  exact ⟨isInfiniteConjugationIsometry_one_add C hQ,
    operatorCommutant_one_add Q,
    (hasNoNontrivialHyperinvariantSubspace_one_add_iff Q).2 hhyper⟩

theorem isInfiniteConjugationIsometry_one_add_of_isConjugation
    {C : H → H} (hC : IsConjugation C) {Q : H →L[ℂ] H}
    (hQ : NormQuasinilpotent Q) :
    IsInfiniteConjugationIsometry hC.toHilbertConjugation (1 + Q) :=
  isInfiniteConjugationIsometry_one_add hC.toHilbertConjugation hQ

omit [CompleteSpace H] in
theorem cho_ko_lee_comparison_of_exists [CompleteSpace H]
    (hex : ∃ Q : H →L[ℂ] H, Q ≠ 0 ∧ NormQuasinilpotent Q ∧
      HasNoNontrivialHyperinvariantSubspace Q) :
    ∃ Q : H →L[ℂ] H, Q ≠ 0 ∧ NormQuasinilpotent Q ∧
      HasNoNontrivialHyperinvariantSubspace Q ∧
      operatorCommutant (1 + Q) = operatorCommutant Q ∧
      ∀ C : H → H, IsConjugation C →
        HasNoNontrivialHyperinvariantSubspace (1 + Q) := by
  obtain ⟨Q, hne, hQ, hhyper⟩ := hex
  exact ⟨Q, hne, hQ, hhyper, operatorCommutant_one_add Q,
    fun _ _ => (hasNoNontrivialHyperinvariantSubspace_one_add_iff Q).2 hhyper⟩

end Invariant233

end

end OAI
