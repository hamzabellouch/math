import Mathlib
import OAI.Computability.VertexCover.Repetition.SelectedProfiles
import OAI.Computability.VertexCover.Repetition.SelectedCommonMarginal

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                     
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionRadius_le_informationRadius [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
      Real.log (1 / G.selectedSuccess strategy selected)) ≤
      selectedInformationRadius G strategy selected := by
  have hcard : (1 : ℝ) ≤ Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) := by
    exact_mod_cast (Nat.succ_le_of_lt
      (Fintype.card_pos : 0 < Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)))
  have hlog := Real.log_nonneg hcard
  have hnonneg : 0 ≤ (Fintype.card {i : Fin n // i ∉ selected} : ℝ) := Nat.cast_nonneg _
  unfold selectedInformationRadius
  apply Real.sqrt_le_sqrt
  nlinarith

theorem selectedQuestionMarginal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive j.1).totalVariation G.questions) ≤
      selectedInformationRadius G strategy selected :=
  (unselectedQuestionMarginal_totalVariation_sum_le_sqrt G strategy selected positive).trans
    (selectedQuestionRadius_le_informationRadius G strategy selected)

def selectedEmbeddingError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  2 * selectedLeftProfileError G strategy selected positive j +
    2 * selectedRightProfileError G strategy selected positive j

theorem selectedEmbeddingError_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    0 ≤ selectedEmbeddingError G strategy selected positive j := by
  exact add_nonneg
    (mul_nonneg (by norm_num) (Information.totalVariation_nonneg _ _))
    (mul_nonneg (by norm_num) (Information.totalVariation_nonneg _ _))

theorem selectedLeftProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedLeftProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedLeftProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hleft := selected_leftReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedRightProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedRightProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedRightProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hright := selected_rightReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedEmbeddingError_sum_le_fifteen [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedEmbeddingError G strategy selected positive j) ≤
      15 * selectedInformationRadius G strategy selected := by
  have hl := selectedLeftProfileError_sum G strategy selected positive
  have hr := selectedRightProfileError_sum G strategy selected positive
  have hn : 0 ≤ selectedInformationRadius G strategy selected := Real.sqrt_nonneg _
  simp only [selectedEmbeddingError, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
