import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.SelectedJointGame
import OAI.Combinatorics.IndependentSets.Repetition.QuestionMarginal
import OAI.Combinatorics.IndependentSets.Repetition.ProfileBounds

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition

section
open scoped BigOperators
open Games Information

theorem finiteDistribution_nonempty {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    Nonempty A := by
  have hsum : (∑ a, μ.weight a) ≠ 0 := by rw [μ.normalized]; norm_num
  obtain ⟨a, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨a⟩

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedProfileFallback (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).pushforward Prod.fst

def selectedLeftProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (x : Q₁) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (leftCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight x)
    (leftCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) x)

def selectedRightProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (y : Q₂) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (rightCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight y)
    (rightCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) y)

def selectedLeftProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

def selectedRightProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

theorem selectedLeftProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedLeftProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (leftRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  leftCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

theorem selectedRightProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedRightProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  rightCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

def selectedSamplingTarget (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Q₁ × Q₂) × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)

theorem selectedSamplingTarget_left_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedLeftProfile G strategy selected positive j z.1.1).weight z.2) =
      selectedLeftProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

theorem selectedSamplingTarget_right_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedRightProfile G strategy selected positive j z.1.2).weight z.2) =
      selectedRightProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

end

open scoped BigOperators
open Games Information

theorem pushforward_snd_weight_eq_secondMarginal {A B : Type*}
    [Fintype A] [Fintype B] (μ : FiniteDistribution (A × B)) :
    (μ.pushforward Prod.snd).weight = secondMarginal μ.weight := by
  classical
  funext b
  simp [FiniteDistribution.pushforward, secondMarginal, Fintype.sum_prod_type]

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealDataSplitEquiv (j : I) :
    (T × (I → X ⊕ Y)) ≃ ((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) where
  toFun z := ((z.1, fun i => z.2 i.1), z.2 j)
  invFun z := (z.1.1, mergeAt j z.2 z.1.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : i = j <;> simp [mergeAt, h]
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        exact mergeAt_other j z.2 z.1.2 i
    · exact mergeAt_self j z.2 z.1.2

theorem partialRevealMarginal_secondMarginal
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    secondMarginal (partialRevealMarginal μ j likelihood) =
      secondMarginal (fullRevealMarginal μ j likelihood) := by
  classical
  funext q
  calc
    _ = ∑ z : (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y),
        maskedJoint (partialRevealMarginal μ j likelihood) (z,q) := by
      simp [secondMarginal, Fintype.sum_prod_type, maskedJoint]
    _ = _ := by
      apply Fintype.sum_equiv (revealDataSplitEquiv (T := T) j).symm
      intro z
      exact (fullRevealMarginal_merge μ j likelihood z.1.1 z.1.2 z.2 q).symm

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedObservationDataEquiv (selected : Finset (Fin n)) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ≃
      (((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
        ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) where
  toFun z := ((z.1.1,z.2),z.1.2)
  invFun z := ((z.1.1,z.2),z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem selectedFullReveal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) =
        secondMarginal (selectedRawMarginal G strategy selected j) := by
  classical
  funext q
  apply Fintype.sum_equiv
    (selectedObservationDataEquiv (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected).symm
  intro z
  exact (selectedRawMarginal_fullReveal G strategy selected j (z,q)).symm

theorem selectedRawMarginal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedRawMarginal G strategy selected j) =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  classical
  funext q
  calc
    _ = (selectedJointLaw G strategy selected positive).probability
        (fun z => decide (z.2 j = q)) := by
      simp only [secondMarginal, selectedRawMarginal, FiniteDistribution.probability,
        selectedJointLaw, toGameLaw, Fintype.sum_prod_type, decide_eq_true_eq]
    _ = ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q)) := by
      have h := selectedJointLaw_question_probability G strategy selected positive
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q))
      simpa [selectedQuestionTuple, mergeCoordinates, j.property] using h
    _ = _ := by
      rw [FiniteDistribution.weight_eq_probability_singleton, selectedQuestionMarginal,
        FiniteDistribution.probability_pushforward]

theorem selectedCommonLaw_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedCommonLaw G strategy selected positive j).weight =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  change secondMarginal (partialRevealMarginal G.questions j
    (selectedOutsideLikelihood G strategy selected)) = _
  rw [partialRevealMarginal_secondMarginal, selectedFullReveal_secondMarginal]
  exact selectedRawMarginal_secondMarginal G strategy selected positive j

theorem selectedCommonLaw_questions_pushforward (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    (selectedCommonLaw G strategy selected positive j).pushforward Prod.snd =
      selectedQuestionMarginal G strategy selected positive j.1 := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro q
  exact (congrFun (pushforward_snd_weight_eq_secondMarginal
    (selectedCommonLaw G strategy selected positive j)) q).trans
      (congrFun (selectedCommonLaw_secondMarginal G strategy selected positive j) q)

end IndependentSetsGames.Foundations.Repetition

end

end OAI
