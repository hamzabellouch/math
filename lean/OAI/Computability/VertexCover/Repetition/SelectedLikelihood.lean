import Mathlib
import OAI.Computability.VertexCover.Repetition.SelectedInformation

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
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLabelAccepts (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : Bool := by
  classical
  exact decide (∀ i : selected, G.accepts (fixed i).1 (fixed i).2 (label.1 i) (label.2 i) = true)

def selectedLocalAnswers {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q)
    (remaining : {i : Fin n // i ∉ selected} → Q) : selected → A :=
  fun i => strategy (mergeCoordinates selected fixed remaining) i.1

def selectedLocalTest {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q) (label : selected → A)
    (remaining : {i : Fin n // i ∉ selected} → Q) : ℝ := by
  classical
  exact if selectedLocalAnswers strategy selected fixed remaining = label then 1 else 0

theorem selectedLocalTest_nonnegative {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q) (label : selected → A)
    (remaining : {i : Fin n // i ∉ selected} → Q) :
    0 ≤ selectedLocalTest strategy selected fixed label remaining := by
  classical
  unfold selectedLocalTest
  split <;> norm_num

omit [Fintype Q₁] [Fintype Q₂] [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionTuple_left (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂) (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (selectedQuestionTuple selected fixed remaining).1 =
      mergeCoordinates selected (fun i => (fixed i).1) (fun i => (remaining i).1) := by
  funext i
  simp only [selectedQuestionTuple, mergeCoordinates]
  split <;> rfl

omit [Fintype Q₁] [Fintype Q₂] [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionTuple_right (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂) (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (selectedQuestionTuple selected fixed remaining).2 =
      mergeCoordinates selected (fun i => (fixed i).2) (fun i => (remaining i).2) := by
  funext i
  simp only [selectedQuestionTuple, mergeCoordinates]
  split <;> rfl

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedWins_of_answerLabel (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂)
    (hlabel : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) = label) :
    G.selectedWins strategy selected (selectedQuestionTuple selected fixed remaining) =
      selectedLabelAccepts G selected fixed label := by
  classical
  have hleft (i : selected) := congrArg (fun l => l.1 i) hlabel
  have hright (i : selected) := congrArg (fun l => l.2 i) hlabel
  apply Bool.eq_iff_iff.mpr
  simp only [Game.selectedWins, selectedLabelAccepts, decide_eq_true_eq]
  constructor
  · intro h i
    have hi := h i.1 i.property
    simpa [Game.coordinateWin, selectedQuestionTuple, mergeCoordinates, i.property,
      ← hleft i, ← hright i, selectedAnswerLabel] using hi
  · intro h i hi
    have hv := h ⟨i,hi⟩
    simpa [Game.coordinateWin, selectedQuestionTuple, mergeCoordinates, hi,
      ← hleft ⟨i,hi⟩, ← hright ⟨i,hi⟩, selectedAnswerLabel] using hv

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    selectedLikelihood G strategy selected fixed label remaining =
      (if selectedLabelAccepts G selected fixed label then 1 else 0) *
        selectedLocalTest strategy.1 selected (fun i => (fixed i).1) label.1 (fun i => (remaining i).1) *
        selectedLocalTest strategy.2 selected (fun i => (fixed i).2) label.2 (fun i => (remaining i).2) := by
  classical
  have he : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) =
      (selectedLocalAnswers strategy.1 selected (fun i => (fixed i).1) (fun i => (remaining i).1),
       selectedLocalAnswers strategy.2 selected (fun i => (fixed i).2) (fun i => (remaining i).2)) := by
    simp only [selectedAnswerLabel,
      selectedQuestionTuple_left, selectedQuestionTuple_right]
    rfl
  by_cases hl : selectedLocalAnswers strategy.1 selected (fun i => (fixed i).1)
      (fun i => (remaining i).1) = label.1
  · by_cases hr : selectedLocalAnswers strategy.2 selected (fun i => (fixed i).2)
        (fun i => (remaining i).2) = label.2
    · have hlabel : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) = label := by
        rw [he, hl, hr]
      simp only [selectedLikelihood, ite_eq_left hlabel,
        selectedWins_of_answerLabel G strategy selected fixed label remaining hlabel,
        selectedLocalTest, ite_eq_left hl, ite_eq_left hr, mul_one]
    · have hn : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) ≠ label := by
        intro h
        rw [he] at h
        exact hr (congrArg Prod.snd h)
      simp [selectedLikelihood, hn, selectedLocalTest, hl, hr]
  · have hn : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) ≠ label := by
      intro h
      rw [he] at h
      exact hl (congrArg Prod.fst h)
    simp [selectedLikelihood, hn, selectedLocalTest, hl]

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
