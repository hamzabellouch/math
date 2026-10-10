import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.SelectedInformation

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition

section
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedJointWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (z : (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) : ℝ :=
  (selectedInputLaw G selected).weight z.1.1 *
    independentProduct (fun i => (selectedInputProfile G selected z.1.1 i).weight) z.2 *
      selectedLikelihood G strategy selected z.1.1.1 z.1.2 z.2 /
        G.selectedSuccess strategy selected

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (z) : 0 ≤ selectedJointWeight G strategy selected z := by
  apply div_nonneg
  · exact mul_nonneg
      (mul_nonneg ((selectedInputLaw G selected).nonnegative _)
        ((independentProduct_isProbability _
          (fun i => gameLaw_isProbability (selectedInputProfile G selected z.1.1 i))).1 z.2))
      (selectedLikelihood_nonnegative G strategy selected z.1.1.1 z.1.2 z.2)
  · exact G.selectedSuccess_nonnegative strategy selected

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) :
    firstMarginal (selectedJointWeight G strategy selected) tv =
      selectedSideWeight G strategy selected tv := by
  simp only [firstMarginal, selectedJointWeight, selectedSideWeight, selectedSideMass,
    div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem selectedJointWeight_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    IsProbability (selectedJointWeight G strategy selected) := by
  constructor
  · exact selectedJointWeight_nonnegative G strategy selected
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedJointWeight G strategy selected) tv) = 1
    simp_rw [selectedJointWeight_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

def selectedJointLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :=
  toGameLaw (selectedJointWeight G strategy selected)
    (selectedJointWeight_isProbability G strategy selected positive)

theorem selectedJointWeight_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) (u) :
    selectedJointWeight G strategy selected (tv,u) =
      (∏ i : selected, G.questions.weight (tv.1.1 i)) *
        (∏ i : {i : Fin n // i ∉ selected}, (revealLaw G.questions).weight (u i,tv.1.2 i)) *
          selectedLikelihood G strategy selected tv.1.1 tv.2 u /
            G.selectedSuccess strategy selected := by
  unfold selectedJointWeight
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    independentProduct, selectedInputProfile]
  rw [mul_assoc (∏ i : selected, G.questions.weight (tv.1.1 i)), reveal_product_factorization]

end
end

open scoped BigOperators
open Information

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_triangle (p q r : α → ℝ) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  have hpoint : ∀ a, |p a - r a| ≤ |p a - q a| + |q a - r a| := by
    intro a
    have := abs_add_le (p a - q a) (q a - r a)
    simpa only [sub_add_sub_cancel] using this
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib] at hsum
  unfold totalVariation
  linarith

noncomputable def conditionWeights (p : α → ℝ) (event : α → Bool) (z : ℝ) : α → ℝ :=
  fun a => if event a then p a / z else 0

theorem conditionWeights_isProbability (p : α → ℝ) (hp : IsProbability p)
    (event : α → Bool) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, (if event a then p a else 0) = z) :
    IsProbability (conditionWeights p event z) := by
  constructor
  · intro a
    dsimp [conditionWeights]
    split
    · exact div_nonneg (hp.1 a) hz.le
    · exact le_rfl
  · have hpoint : ∀ a, conditionWeights p event z a =
        (if event a then p a else 0) / z := by
      intro a
      simp only [conditionWeights]
      split <;> simp
    simp only [hpoint, div_eq_mul_inv, ← Finset.sum_mul, hmass, mul_inv_cancel₀ hz.ne']

theorem totalVariation_condition_le (p q : α → ℝ) (event : α → Bool)
    {z : ℝ} (hz : 0 < z) :
    totalVariation (conditionWeights p event z) (conditionWeights q event z) ≤
      totalVariation p q / z := by
  have hpoint : ∀ a,
      |conditionWeights p event z a - conditionWeights q event z a| ≤
        |p a - q a| / z := by
    intro a
    dsimp [conditionWeights]
    split
    · rw [← sub_div, abs_div, abs_of_pos hz]
    · simp only [sub_self, abs_zero]
      positivity
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [div_eq_mul_inv, ← Finset.sum_mul] at hsum
  have hsum' : (∑ a, |conditionWeights p event z a - conditionWeights q event z a|) ≤
      (∑ a, |p a - q a|) / z := by
    simpa only [div_eq_mul_inv] using hsum
  unfold totalVariation
  calc
    _ ≤ (∑ a, |p a - q a|) / z / 2 := div_le_div_of_nonneg_right hsum' (by norm_num)
    _ = _ := by ring

theorem totalVariation_condition_half_le (p q : α → ℝ) (event : α → Bool) :
    totalVariation (conditionWeights p event (1 / 2))
      (conditionWeights q event (1 / 2)) ≤ 2 * totalVariation p q := by
  have h := totalVariation_condition_le p q event (z := 1 / 2) (by norm_num)
  convert h using 1
  ring

theorem totalVariation_append_kernel (p q : α → ℝ) (kernel : α → β → ℝ)
    (hk : ∀ a, IsProbability (kernel a)) :
    totalVariation (fun ab : α × β => p ab.1 * kernel ab.1 ab.2)
      (fun ab : α × β => q ab.1 * kernel ab.1 ab.2) = totalVariation p q := by
  unfold totalVariation
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have habs : ∀ b, |kernel a b| = kernel a b := fun b => abs_of_nonneg ((hk a).1 b)
  simp only [← sub_mul, abs_mul, habs, ← Finset.mul_sum, (hk a).2,
    mul_one]

noncomputable def kernelPushforward (p : α → ℝ) (kernel : α → β → ℝ) : β → ℝ :=
  fun b => ∑ a, p a * kernel a b

theorem totalVariation_kernelPushforward_le (p q : α → ℝ) (kernel : α → β → ℝ)
    (hk : ∀ a, IsProbability (kernel a)) :
    totalVariation (kernelPushforward p kernel) (kernelPushforward q kernel) ≤
      totalVariation p q := by
  have hpoint : ∀ b,
      |kernelPushforward p kernel b - kernelPushforward q kernel b| ≤
        ∑ a, |p a - q a| * kernel a b := by
    intro b
    simp only [kernelPushforward, ← Finset.sum_sub_distrib, ← sub_mul]
    have h := Finset.abs_sum_le_sum_abs (fun a => (p a - q a) * kernel a b) Finset.univ
    have habs : ∀ a, |kernel a b| = kernel a b := fun a => abs_of_nonneg ((hk a).1 b)
    simpa only [abs_mul, habs] using h
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset β)) => hpoint b)
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.mul_sum, (hk _).2, mul_one] at hsum
  exact div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)

end IndependentSetsGames.Foundations.Repetition

end OAI
