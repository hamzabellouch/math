import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.SelectedCompletionGame
import OAI.Combinatorics.IndependentSets.Repetition.LocalSimulation
import OAI.Combinatorics.IndependentSets.Repetition.SelectionSequence

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition.SelectionSequence
open IndependentSetsGames.Foundations.Games

variable {Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
variable [Nonempty A₁] [Nonempty A₂]

def ConditionalCoordinateBound (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (_hcard : S.card < n)
    (hp : 0 < G.selectedSuccess strategy S),
    ∃ j, j ∉ S ∧
      (((G.repetition n).questions.condition (G.selectedWins strategy S) hp).probability
        (G.coordinateWin strategy j)) ≤
        G.value + 15 * Real.sqrt
          (((S.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy S)) /
            ((n : ℝ) - S.card))

theorem repetition_success_le_of_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hcoordinate : ConditionalCoordinateBound G n strategy ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) := by
  have hpositive : ∀ S : Finset (Fin n), S.card < n →
      0 < G.selectedSuccess strategy S →
      ∃ j, j ∉ S ∧ SetStep (G.selectedSuccess strategy) v ell S j := by
    intro S hcard hp
    obtain ⟨j, hj, hbound⟩ := hcoordinate S hcard hp
    refine ⟨j, hj, ?_⟩
    change G.selectedSuccess strategy (insert j S) ≤ _
    rw [G.selectedSuccess_insert strategy S j hp]
    exact mul_le_mul_of_nonneg_left
      (hbound.trans (add_le_add hvalue (le_refl _))) (le_of_lt hp)
  obtain ⟨p, hp0, hpnonneg, hpmono, hrec, hpn⟩ :=
    exists_scalar_sequence (G.selectedSuccess strategy) v ell
      (G.selectedSuccess_empty strategy) (G.selectedSuccess_nonnegative strategy)
      (G.selectedSuccess_antitone strategy) hpositive
  have hbound := scalar_bound_6000 p n
    (G.value_nonnegative.trans hvalue) hv1 hell hp0 hpnonneg hpmono hrec
  rw [hpn, G.selectedSuccess_univ strategy] at hbound
  exact hbound

end IndependentSetsGames.Foundations.Repetition.SelectionSequence

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_coordinate_probability_le_value_add_error
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
      (G.coordinateWin strategy j.1) ≤
        G.value + selectedEmbeddingError G strategy selected positive j := by
  classical
  let : Nonempty (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
    finiteDistribution_nonempty (selectedProfileFallback G strategy selected positive j)
  have h := coordinate_probability_le_value_of_local_completion G j.1 strategy
    (selectedSamplingTarget G strategy selected positive j)
    (selectedLeftProfile G strategy selected positive j)
    (selectedRightProfile G strategy selected positive j)
    (selectedFullLeftCompletion G strategy selected j)
    (selectedFullRightCompletion G strategy selected j)
    (selectedFullLeftCompletion_support G strategy selected j)
    (selectedFullRightCompletion_support G strategy selected j)
    (Classical.choice inferInstance)
  have htarget : (selectedSamplingTarget G strategy selected positive j).mixture
      (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
        (selectedFullRightCompletion G strategy selected j (z.1.2,z.2))) =
      (G.repetition n).questions.condition (G.selectedWins strategy selected) positive :=
    selectedFullCompletionMixture_eq_conditionedQuestions G strategy selected positive j
  rw [htarget, selectedSamplingTarget_left_error, selectedSamplingTarget_right_error] at h
  exact h

theorem holenstein_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    SelectionSequence.ConditionalCoordinateBound G n strategy ell := by
  intro selected hcard positive
  obtain ⟨j,hj⟩ := exists_coordinate_le_information_budget G strategy selected positive ell
    halphabet hcard (selectedEmbeddingError G strategy selected positive)
    (selectedEmbeddingError_sum_le_fifteen G strategy selected positive)
  exact ⟨j.1,j.property,
    (selected_coordinate_probability_le_value_add_error G strategy selected positive j).trans
      (add_le_add le_rfl hj)⟩

theorem holenstein_repetition_success
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) :=
  SelectionSequence.repetition_success_le_of_conditionalCoordinateBound G n strategy
    hvalue hv hell (holenstein_conditionalCoordinateBound G n strategy ell halphabet)

theorem holenstein_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).value ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) := by
  apply ((G.repetition n).value_le_iff _).2
  intro strategy
  exact holenstein_repetition_success G n strategy hvalue hv hell halphabet

end
end IndependentSetsGames.Foundations.Repetition

end OAI
