import OAI.Analysis.KadisonKastler.FiniteStageEmbedding
import OAI.Analysis.KadisonKastler.StandardTracialCommutant
import OAI.Analysis.KadisonKastler.ExpectedModularPreparation

namespace OAI

/-! # Aligning the right action of a common increasing matrix algebra -/

namespace KadisonKastler

noncomputable section

open Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] {M N R : VonNeumannAlgebra H}

theorem exists_matrix_right_alignment
    (p : StandardTracialPosition M) (hRM : R ≤ M) (hRN : R ≤ N)
    (d : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hsmall : ρ ≤ 1 / 1152)
    (hnear : NearInclusion M.commutant N.commutant ρ) :
    ∃ w : unitary (H →L[ℂ] H),
      (w : H →L[ℂ] H) ∈ R.commutant ∧
      R ≤ unitaryConjugateAlgebra (star w) N ∧
      conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤
        (unitaryConjugateAlgebra (star w) N).commutant ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 84 * ρ := by
  let S := conjugateRightAlgebra p.conjugation p.conjugation_involutive R
  have hSM : S ≤ M.commutant := by
    rw [← p.conjugate_algebra_eq_commutant]
    exact conjugateRightAlgebra_mono p.conjugation p.conjugation_involutive hRM
  have hSR : S ≤ R.commutant := by
    intro x hx
    exact VonNeumannAlgebra.mem_commutant_iff.mpr (fun r hr =>
      VonNeumannAlgebra.mem_commutant_iff.mp (hSM hx) r (hRM hr))
  have hS : S = generatedVonNeumannAlgebra
      (⨆ n, (conjugateMatrixUnits p.conjugation p.conjugation_involutive (E n)).algebra) := by
    dsimp [S]
    rw [hR]
    exact conjugateRightAlgebra_generated_matrixStages _ _ d E
  obtain ⟨w, hw, hmove, hn⟩ := exists_localized_unitary_matrixUnits_embedding d
    (fun n => conjugateMatrixUnits p.conjugation p.conjugation_involutive (E n))
    (conjugateMatrixUnits_mono _ _ d E hmono) hS hρ hsmall
    (nearInclusion_mono_left hSM hnear)
  have hfix := generated_right_correction_le_commutant R S N hRN hSR hw
  obtain ⟨hleft, hright⟩ := preparedPair_second_correction R S N hRN hSR w hw hmove
  exact ⟨w, hfix, hleft, hright, hn⟩

end

end KadisonKastler

end OAI
