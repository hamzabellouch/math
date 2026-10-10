import Mathlib
import OAI.Computability.MinUncut.PCP.Completion
import OAI.Computability.MinUncut.Games.Pinsker

namespace OAI

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

def mergeCoordinates {Ω : Type*} {n : Nat} (selected : Finset (Fin n))
    (fixed : selected → Ω) (remaining : {i : Fin n // i ∉ selected} → Ω) : Fin n → Ω :=
  fun i => if h : i ∈ selected then fixed ⟨i,h⟩ else remaining ⟨i,h⟩

def coordinateSplitEquiv {Ω : Type*} {n : Nat} (selected : Finset (Fin n)) :
    (Fin n → Ω) ≃ ((selected → Ω) × ({i : Fin n // i ∉ selected} → Ω)) where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun x := mergeCoordinates selected x.1 x.2
  left_inv x := by funext i; simp [mergeCoordinates]
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp [mergeCoordinates, i.property]

theorem iid_coordinate_split {Ω : Type*} [Fintype Ω] {n : Nat}
    (μ : FiniteDistribution Ω) (selected : Finset (Fin n)) :
    (μ.iid n).transport (coordinateSplitEquiv selected) =
      (FiniteDistribution.table (fun _ : selected => μ)).product
        (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => μ)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, μ.weight (mergeCoordinates selected x.1 x.2 i)) =
    (∏ i : selected, μ.weight (x.1 i)) *
      ∏ i : {i : Fin n // i ∉ selected}, μ.weight (x.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ∈ selected)
    (fun i => μ.weight (mergeCoordinates selected x.1 x.2 i))
  have hi : Subtype.fintype (fun i : Fin n => i ∈ selected) =
      Finset.Subtype.fintype selected := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : {i : Fin n // i ∈ selected},
        μ.weight (mergeCoordinates selected x.1 x.2 i.1)) *
        ∏ i : {i : Fin n // i ∉ selected},
          μ.weight (mergeCoordinates selected x.1 x.2 i.1) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [mergeCoordinates, i.property]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

abbrev SelectedLabels (selected : Finset (Fin n)) :=
  (selected → A₁) × (selected → A₂)

def selectedQuestionTuple (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (Fin n → Q₁) × (Fin n → Q₂) :=
  (fun i => (mergeCoordinates selected fixed remaining i).1,
   fun i => (mergeCoordinates selected fixed remaining i).2)

def selectedAnswerLabel
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    SelectedLabels (A₁ := A₁) (A₂ := A₂) selected :=
  (fun i => strategy.1 questions.1 i.1, fun i => strategy.2 questions.2 i.1)

def selectedLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ := by
  classical
  let questions := selectedQuestionTuple selected fixed remaining
  exact if selectedAnswerLabel strategy selected questions = label then
    (if G.selectedWins strategy selected questions then 1 else 0) else 0

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    0 ≤ selectedLikelihood G strategy selected fixed label remaining := by
  classical
  dsimp only [selectedLikelihood]
  split_ifs <;> norm_num

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (∑ label, selectedLikelihood G strategy selected fixed label remaining) =
      if G.selectedWins strategy selected (selectedQuestionTuple selected fixed remaining)
      then 1 else 0 := by
  classical
  simp [selectedLikelihood]

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_sum_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (∑ label, selectedLikelihood G strategy selected fixed label remaining) ≤ 1 := by
  rw [selectedLikelihood_sum]
  split <;> norm_num

def selectedSplitLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution ((selected → Q₁ × Q₂) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => G.questions))

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (selectedSplitLaw G selected).probability
      (fun q => G.selectedWins strategy selected (selectedQuestionTuple selected q.1 q.2)) =
        G.selectedSuccess strategy selected := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability _
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

abbrev SelectedInput (Q₁ Q₂ : Type*) {n : Nat} (selected : Finset (Fin n)) :=
  (selected → Q₁ × Q₂) × ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)

def selectedInputLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution (SelectedInput Q₁ Q₂ selected) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => revealInputLaw G.questions))

def selectedInputProfile (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (t : SelectedInput Q₁ Q₂ selected) (i : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (Q₁ × Q₂) := revealProfile G.questions (t.2 i)

def selectedSideMass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  ∑ u, independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
    selectedLikelihood G strategy selected tv.1.1 tv.2 u

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSideMass_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (t : SelectedInput Q₁ Q₂ selected) :
    (∑ v, selectedSideMass G strategy selected (t,v)) =
      ∑ u, independentProduct (fun i => (selectedInputProfile G selected t i).weight) u *
        (if G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u)
        then 1 else 0) := by
  classical
  simp only [selectedSideMass]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, selectedLikelihood_sum]

theorem selectedSideMass_total (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (∑ tv, (selectedInputLaw G selected).weight tv.1 *
      selectedSideMass G strategy selected tv) = G.selectedSuccess strategy selected := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, selectedSideMass_sum]
  rw [Fintype.sum_prod_type]
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    selectedInputProfile, independentProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hforget (fixed : selected → Q₁ × Q₂) :=
    reveal_product_expectation G.questions
      (fun u : {i : Fin n // i ∉ selected} → Q₁ × Q₂ =>
        if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u)
        then (1 : ℝ) else 0)
  simp_rw [hforget]
  have h := selectedSplit_probability G strategy selected
  simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.table, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_assoc] using h

def selectedSideWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  (selectedInputLaw G selected).weight tv.1 * selectedSideMass G strategy selected tv /
    G.selectedSuccess strategy selected

theorem selected_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected}, totalVariation
      (fun tva : (SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) × (Q₁ × Q₂) =>
        selectedSideWeight G strategy selected tva.1 * coordinateMarginal
          (posteriorOrOriginal
            (independentProduct (fun j => (selectedInputProfile G selected tva.1.1 j).weight))
            (selectedLikelihood G strategy selected tva.1.1.1 tva.1.2)
            (selectedSideMass G strategy selected tva.1)) i tva.2)
      (fun tva => selectedSideWeight G strategy selected tva.1 *
        (selectedInputProfile G selected tva.1.1 i).weight tva.2)) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  exact finite_side_information_bound (selectedInputLaw G selected).weight
    (fun t i => (selectedInputProfile G selected t i).weight)
    (fun tv => selectedLikelihood G strategy selected tv.1.1 tv.2)
    (selectedSideMass G strategy selected) (selectedSideWeight G strategy selected)
    (gameLaw_isProbability _) (fun t i => gameLaw_isProbability _)
    (fun tv => selectedLikelihood_nonnegative G strategy selected tv.1.1 tv.2)
    (fun t => selectedLikelihood_sum_le_one G strategy selected t.1)
    (fun _ => rfl) positive (selectedSideMass_total G strategy selected) (fun _ => rfl)

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
  convert h using 1; ring

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

open scoped BigOperators
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def maskedJoint (p : S × (X × Y) → ℝ) : (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  (if z.1.2 = Sum.inl z.2.1 then p (z.1.1, z.2) / 2 else 0) +
  (if z.1.2 = Sum.inr z.2.2 then p (z.1.1, z.2) / 2 else 0)

def maskedModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (maskedJoint p) z.1 * (revealProfile μ z.1.2).weight z.2

def leftRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ y, p (z.1, (z.2.1, y))) * (revealProfile μ (Sum.inl z.2.1)).weight z.2

def rightRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ x, p (z.1, (x, z.2.2))) * (revealProfile μ (Sum.inr z.2.2)).weight z.2

theorem sum_maskedJoint (p : S × (X × Y) → ℝ) :
    (∑ z, maskedJoint p z) = ∑ z, p z := by
  classical
  have hrow (s : S) (q : X × Y) :
      (∑ r : X ⊕ Y, maskedJoint p ((s,r),q)) = p (s,q) := by
    simp [maskedJoint]
  calc
    _ = ∑ s : S, ∑ r : X ⊕ Y, ∑ q : X × Y, maskedJoint p ((s,r),q) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ s : S, ∑ q : X × Y, p (s,q) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      simp_rw [hrow]
    _ = _ := (Fintype.sum_prod_type _).symm

theorem maskedJoint_isProbability_iff (p : S × (X × Y) → ℝ) :
    Information.IsProbability (maskedJoint p) ↔ Information.IsProbability p := by
  classical
  constructor
  · intro h
    constructor
    · intro z
      have hp := h.1 ((z.1,Sum.inl z.2.1),z.2)
      simp [maskedJoint] at hp
      linarith
    · rw [← sum_maskedJoint]
      exact h.2
  · intro h
    constructor
    · intro z
      have hp : 0 ≤ p (z.1.1,z.2) / 2 := div_nonneg (h.1 _) (by norm_num)
      dsimp [maskedJoint]
      split_ifs <;> linarith
    · rw [sum_maskedJoint]
      exact h.2

omit [Fintype S] in
theorem maskedJoint_firstMarginal_inl (p : S × (X × Y) → ℝ) (s : S) (x : X) :
    Information.firstMarginal (maskedJoint p) (s, Sum.inl x) =
      (∑ y, p (s, (x, y))) / 2 := by
  simp [Information.firstMarginal, maskedJoint, Fintype.sum_prod_type,
    div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

omit [Fintype S] in
theorem maskedJoint_firstMarginal_inr (p : S × (X × Y) → ℝ) (s : S) (y : Y) :
    Information.firstMarginal (maskedJoint p) (s, Sum.inr y) =
      (∑ x, p (s, (x, y))) / 2 := by
  simp [Information.firstMarginal, maskedJoint, Fintype.sum_prod_type,
    div_eq_mul_inv, Finset.sum_mul]

private theorem abs_half_sub_half_mul (a b c : ℝ) :
    |a / 2 - b / 2 * c| = |a - b * c| / 2 := by
  rw [show a / 2 - b / 2 * c = (a - b * c) / 2 by ring, abs_div]
  norm_num

omit [Fintype S] in
theorem abs_masked_inl (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) (s : S) (u x : X) (y : Y) :
    |maskedJoint p ((s, Sum.inl u), (x, y)) - maskedModel μ p ((s, Sum.inl u), (x, y))| =
      if x = u then |p (s, (x, y)) - leftRevealModel μ p (s, (x, y))| / 2 else 0 := by
  by_cases hx : x = u
  · subst x
    simp only [maskedModel, maskedJoint_firstMarginal_inl]
    simpa [maskedJoint, leftRevealModel] using
      abs_half_sub_half_mul (p (s, (u, y))) (∑ v, p (s, (u, v)))
        ((revealProfile μ (Sum.inl u)).weight (u, y))
  · have hs := revealProfile_inl_support μ u (x, y) hx
    simp [maskedJoint, maskedModel, hs, hx, Ne.symm hx]

omit [Fintype S] in
theorem abs_masked_inr (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) (s : S) (v : Y) (x : X) (y : Y) :
    |maskedJoint p ((s, Sum.inr v), (x, y)) - maskedModel μ p ((s, Sum.inr v), (x, y))| =
      if y = v then |p (s, (x, y)) - rightRevealModel μ p (s, (x, y))| / 2 else 0 := by
  by_cases hy : y = v
  · subst y
    simp only [maskedModel, maskedJoint_firstMarginal_inr]
    simpa [maskedJoint, rightRevealModel] using
      abs_half_sub_half_mul (p (s, (x, v))) (∑ u, p (s, (u, v)))
        ((revealProfile μ (Sum.inr v)).weight (x, v))
  · have hs := revealProfile_inr_support μ v (x, y) hy
    simp [maskedJoint, maskedModel, hs, hy, Ne.symm hy]

theorem masked_totalVariation_identity (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) =
      Information.totalVariation p (leftRevealModel μ p) +
        Information.totalVariation p (rightRevealModel μ p) := by
  have hleft (s : S) :
      (∑ u : X, ∑ q : X × Y,
        |maskedJoint p ((s, Sum.inl u), q) - maskedModel μ p ((s, Sum.inl u), q)|) =
      (∑ q : X × Y, |p (s, q) - leftRevealModel μ p (s, q)|) / 2 := by
    simp_rw [Fintype.sum_prod_type, abs_masked_inl]
    simp [Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]
  have hright (s : S) :
      (∑ v : Y, ∑ q : X × Y,
        |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|) =
      (∑ q : X × Y, |p (s, q) - rightRevealModel μ p (s, q)|) / 2 := by
    have hcollapse :
        (∑ v : Y, ∑ q : X × Y,
          |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|) =
        ∑ v : Y, ∑ x : X, |p (s, (x, v)) - rightRevealModel μ p (s, (x, v))| / 2 := by
      simp [Fintype.sum_prod_type, abs_masked_inr]
    rw [hcollapse, Finset.sum_comm]
    simp [Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_mul]
  have hmass :
      (∑ z : (S × (X ⊕ Y)) × (X × Y), |maskedJoint p z - maskedModel μ p z|) =
      ((∑ z : S × (X × Y), |p z - leftRevealModel μ p z|) +
       (∑ z : S × (X × Y), |p z - rightRevealModel μ p z|)) / 2 := by
    calc
      _ = ∑ s : S,
          ((∑ u : X, ∑ q : X × Y, |maskedJoint p ((s, Sum.inl u), q) - maskedModel μ p ((s, Sum.inl u), q)|) +
           (∑ v : Y, ∑ q : X × Y, |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|)) := by
        simp only [Fintype.sum_prod_type, Fintype.sum_sum_type]
      _ = ∑ s : S,
          ((∑ q : X × Y, |p (s, q) - leftRevealModel μ p (s, q)|) / 2 +
           (∑ q : X × Y, |p (s, q) - rightRevealModel μ p (s, q)|) / 2) := by
        simp_rw [hleft, hright]
      _ = _ := by
        simp [Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul, add_mul]
  unfold Information.totalVariation
  rw [hmass]
  ring

theorem leftRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (leftRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (rightRevealModel μ p)]

theorem rightRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (rightRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (leftRevealModel μ p)]

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def mergeAt {R : Type*} (j : I) (a : R) (rest : {i : I // i ≠ j} → R) : I → R :=
  fun i => if h : i = j then a else rest ⟨i,h⟩

omit [Fintype I] in
@[simp] theorem mergeAt_self {R : Type*} (j : I) (a : R) (rest : {i : I // i ≠ j} → R) :
    mergeAt j a rest j = a := by simp [mergeAt]

omit [Fintype I] in
@[simp] theorem mergeAt_other {R : Type*} (j : I) (a : R)
    (rest : {i : I // i ≠ j} → R) (i : {i : I // i ≠ j}) :
    mergeAt j a rest i.1 = rest i := by simp [mergeAt, i.property]

def partialRevealWeight (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) : ℝ :=
  μ.weight (u j) * ∏ i : {i : I // i ≠ j}, (revealLaw μ).weight (u i.1,rest i)

theorem product_reveal_at (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (r : X ⊕ Y) (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    (∏ i, (revealLaw μ).weight (u i,mergeAt j r rest i)) =
      (if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
      (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [mergeAt_self, mergeAt_other, revealLaw_weight]
  by_cases hl : r = Sum.inl (u j).1 <;> by_cases hr : r = Sum.inr (u j).2 <;>
    simp [hl, hr, partialRevealWeight, revealLaw_weight] <;> ring

def partialRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    partialRevealWeight μ j z.1.2 u * likelihood z.1.1 u else 0

def fullRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    (∏ i, (revealLaw μ).weight (u i,z.1.2 i)) * likelihood z.1.1 u else 0

omit [Fintype T] in
theorem fullRevealMarginal_merge (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) (t : T)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (r : X ⊕ Y) (q : X × Y) :
    fullRevealMarginal μ j likelihood ((t,mergeAt j r rest),q) =
      maskedJoint (partialRevealMarginal μ j likelihood) (((t,rest),r),q) := by
  classical
  unfold fullRevealMarginal
  simp_rw [product_reveal_at]
  have hpoint (u : I → X × Y) :
      (if u j = q then
        ((if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
         (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0)) *
          likelihood t u else 0) =
      (if r = Sum.inl q.1 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) +
      (if r = Sum.inr q.2 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) := by
    by_cases hu : u j = q
    · rw [hu]
      by_cases hl : r = Sum.inl q.1 <;> by_cases hr : r = Sum.inr q.2 <;>
        simp [hl, hr] <;> ring
    · simp [hu]
  simp_rw [hpoint]
  simp [maskedJoint, partialRevealMarginal, Finset.sum_add_distrib,
    Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]

def fullRevealModel (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (fullRevealMarginal μ j likelihood) z.1 *
    (revealProfile μ (z.1.2 j)).weight z.2

omit [Fintype T] in
theorem fullRevealModel_merge (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) (t : T)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (r : X ⊕ Y) (q : X × Y) :
    fullRevealModel μ j likelihood ((t,mergeAt j r rest),q) =
      maskedModel μ (partialRevealMarginal μ j likelihood) (((t,rest),r),q) := by
  simp only [fullRevealModel, Information.firstMarginal, fullRevealMarginal_merge,
    mergeAt_self, maskedModel]

def revealSplitEquiv (j : I) :
    ((T × (I → X ⊕ Y)) × (X × Y)) ≃
      (((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) × (X × Y)) where
  toFun z := (((z.1.1, fun i => z.1.2 i.1), z.1.2 j), z.2)
  invFun z := ((z.1.1.1, mergeAt j z.1.2 z.1.1.2), z.2)
  left_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        by_cases h : i = j <;> simp [mergeAt, h]
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext i
          exact mergeAt_other j z.1.2 z.1.1.2 i
      · exact mergeAt_self j z.1.2 z.1.1.2
    · rfl

theorem totalVariation_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p q : B → ℝ) :
    Information.totalVariation (fun a => p (e a)) (fun a => q (e a)) =
      Information.totalVariation p q := by
  unfold Information.totalVariation
  congr 1
  exact e.sum_comp (fun b => |p b - q b|)

theorem fullReveal_totalVariation (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (fullRevealMarginal μ j likelihood) (fullRevealModel μ j likelihood) =
      Information.totalVariation (maskedJoint (partialRevealMarginal μ j likelihood))
        (maskedModel μ (partialRevealMarginal μ j likelihood)) := by
  calc
    _ = Information.totalVariation
        (fun z => fullRevealMarginal μ j likelihood ((revealSplitEquiv (T := T) j).symm z))
        (fun z => fullRevealModel μ j likelihood ((revealSplitEquiv (T := T) j).symm z)) :=
      (totalVariation_comp_equiv (revealSplitEquiv (T := T) j).symm _ _).symm
    _ = _ := by
      congr 1 <;> funext z
      · exact fullRevealMarginal_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2
      · exact fullRevealModel_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2

theorem leftReveal_full_error (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (partialRevealMarginal μ j likelihood)
      (leftRevealModel μ (partialRevealMarginal μ j likelihood)) ≤
      2 * Information.totalVariation (fullRevealMarginal μ j likelihood)
        (fullRevealModel μ j likelihood) := by
  rw [fullReveal_totalVariation]
  exact leftRevealModel_totalVariation_le μ _

theorem rightReveal_full_error (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (partialRevealMarginal μ j likelihood)
      (rightRevealModel μ (partialRevealMarginal μ j likelihood)) ≤
      2 * Information.totalVariation (fullRevealMarginal μ j likelihood)
        (fullRevealModel μ j likelihood) := by
  rw [fullReveal_totalVariation]
  exact rightRevealModel_totalVariation_le μ _

end
end MinUncutGames.Foundations.Repetition

end OAI
