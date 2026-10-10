import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.SelectedJoint
import OAI.Combinatorics.IndependentSets.Repetition.PartialReveal

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedRawMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then selectedJointWeight G strategy selected (z.1,u) else 0

theorem selectedPosterior_eq_raw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (tv) (q) :
    selectedSideWeight G strategy selected tv * coordinateMarginal
      (posteriorOrOriginal
        (independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight))
        (selectedLikelihood G strategy selected tv.1.1 tv.2)
        (selectedSideMass G strategy selected tv)) j q =
      selectedRawMarginal G strategy selected j (tv,q) := by
  classical
  rw [selectedSideWeight]
  have h := weighted_coordinate_posterior_recombine
    (independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight))
    (selectedLikelihood G strategy selected tv.1.1 tv.2)
    (independentProduct_isProbability _
      (fun i => gameLaw_isProbability (selectedInputProfile G selected tv.1 i)))
    (selectedLikelihood_nonnegative G strategy selected tv.1.1 tv.2)
    (c := selectedSideMass G strategy selected tv) rfl
    ((selectedInputLaw G selected).weight tv.1) (G.selectedSuccess strategy selected) j q
  rw [h]
  simp only [Finset.mul_sum, selectedRawMarginal, selectedJointWeight]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u j = q
  · simp only [ite_eq_left hu]
    ring
  · simp [hu]

theorem selectedRawMarginal_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (tv) :
    firstMarginal (selectedRawMarginal G strategy selected j) tv =
      selectedSideWeight G strategy selected tv := by
  classical
  simp only [firstMarginal, selectedRawMarginal]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact selectedJointWeight_firstMarginal G strategy selected tv

theorem selectedRawMarginal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (selectedRawMarginal G strategy selected j) := by
  classical
  constructor
  · intro z
    apply Finset.sum_nonneg
    intro u _
    split
    · exact selectedJointWeight_nonnegative G strategy selected (z.1,u)
    · exact le_rfl
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedRawMarginal G strategy selected j) tv) = 1
    simp_rw [selectedRawMarginal_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

theorem selected_raw_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, totalVariation
      (selectedRawMarginal G strategy selected j)
      (fun z => selectedSideWeight G strategy selected z.1 *
        (selectedInputProfile G selected z.1.1 j).weight z.2)) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  have h := selected_information_bound G strategy selected positive
  simp_rw [selectedPosterior_eq_raw] at h
  exact h

def selectedOutsideLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (u : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ :=
  (∏ i : selected, G.questions.weight (t.1 i)) *
    selectedLikelihood G strategy selected t.1 t.2 u / G.selectedSuccess strategy selected

def selectedObservationEquiv (selected : Finset (Fin n)) :
    ((SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂)) ≃
    ((((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) × (Q₁ × Q₂)) where
  toFun z := (((z.1.1.1,z.1.2),z.1.1.2),z.2)
  invFun z := (((z.1.1.1,z.1.2),z.1.1.2),z.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem selectedRawMarginal_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (z) :
    selectedRawMarginal G strategy selected j
        ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) z := by
  classical
  change selectedRawMarginal G strategy selected j
    (((z.1.1.1,z.1.2),z.1.1.2),z.2) = _
  simp only [selectedRawMarginal, fullRevealMarginal]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u j = z.2
  · simp only [ite_eq_left hu, selectedJointWeight_factorization, selectedOutsideLikelihood]
    ring
  · simp [hu]

theorem selectedRawReference_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (z) :
    (fun w => selectedSideWeight G strategy selected w.1 *
      (selectedInputProfile G selected w.1.1 j).weight w.2)
        ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z) =
      fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected) z := by
  change selectedSideWeight G strategy selected ((z.1.1.1,z.1.2),z.1.1.2) *
    (revealProfile G.questions (z.1.2 j)).weight z.2 = _
  rw [← selectedRawMarginal_firstMarginal G strategy selected j]
  unfold firstMarginal fullRevealModel
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact selectedRawMarginal_fullReveal G strategy selected j (z.1,q)

theorem selected_raw_error_eq_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedRawMarginal G strategy selected j)
      (fun z => selectedSideWeight G strategy selected z.1 *
        (selectedInputProfile G selected z.1.1 j).weight z.2) =
      totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
  rw [← totalVariation_comp_equiv
    (selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm]
  congr 1 <;> funext z
  · exact selectedRawMarginal_fullReveal G strategy selected j z
  · exact selectedRawReference_fullReveal G strategy selected j z

theorem selected_fullReveal_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected))) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  have h := selected_raw_information_bound G strategy selected positive
  simp_rw [selected_raw_error_eq_fullReveal] at h
  exact h

def selectedInformationRadius (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
    (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
      Real.log (1 / G.selectedSuccess strategy selected)))

theorem selected_leftReveal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (leftRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected)))) ≤
      2 * selectedInformationRadius G strategy selected := by
  calc
    _ ≤ ∑ j : {i : Fin n // i ∉ selected},
        2 * totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
      apply Finset.sum_le_sum
      intro j _
      exact leftReveal_full_error G.questions j _
    _ = 2 * ∑ j : {i : Fin n // i ∉ selected},
        totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (selected_fullReveal_information_bound G strategy selected positive) (by norm_num)

theorem selected_rightReveal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected)))) ≤
      2 * selectedInformationRadius G strategy selected := by
  calc
    _ ≤ ∑ j : {i : Fin n // i ∉ selected},
        2 * totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
      apply Finset.sum_le_sum
      intro j _
      exact rightReveal_full_error G.questions j _
    _ = 2 * ∑ j : {i : Fin n // i ∉ selected},
        totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (selected_fullReveal_information_bound G strategy selected positive) (by norm_num)

end
end IndependentSetsGames.Foundations.Repetition

end OAI
