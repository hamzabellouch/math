import Mathlib
import OAI.Computability.DirectedFeedback.Probability.TraceLaw

namespace OAI


namespace DFVSGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def firstMarginal (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

noncomputable def secondMarginal (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

def product (p : α → ℝ) (q : β → ℝ) : α × β → ℝ := fun ab => p ab.1 * q ab.2

theorem firstMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (firstMarginal p) := by
  constructor
  · intro a
    exact Finset.sum_nonneg (fun b _ => hp.1 (a, b))
  · simpa only [firstMarginal, Fintype.sum_prod_type] using hp.2

theorem secondMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (secondMarginal p) := by
  constructor
  · intro b
    exact Finset.sum_nonneg (fun a _ => hp.1 (a, b))
  · change (∑ b, ∑ a, p (a, b)) = 1
    rw [Finset.sum_comm]
    exact (firstMarginal_isProbability p hp).2

theorem product_isProbability (p : α → ℝ) (q : β → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) : IsProbability (product p q) := by
  constructor
  · intro ab
    exact mul_nonneg (hp.1 ab.1) (hq.1 ab.2)
  · simp only [product, Fintype.sum_prod_type, ← Finset.mul_sum, hq.2, mul_one, hp.2]

theorem point_le_firstMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ firstMarginal p a := by
  classical
  exact Finset.single_le_sum (fun b _ => hp.1 (a, b)) (Finset.mem_univ b)

theorem point_le_secondMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ secondMarginal p b := by
  classical
  exact Finset.single_le_sum (fun a _ => hp.1 (a, b)) (Finset.mem_univ a)

theorem joint_supportedBy_product_marginals (p : α × β → ℝ) (hp : IsProbability p) :
    SupportedBy p (product (firstMarginal p) (secondMarginal p)) := by
  intro ab hpne
  have hpos : 0 < p ab := lt_of_le_of_ne (hp.1 ab) (Ne.symm hpne)
  exact mul_ne_zero
    (ne_of_gt (hpos.trans_le (point_le_firstMarginal p hp ab.1 ab.2)))
    (ne_of_gt (hpos.trans_le (point_le_secondMarginal p hp ab.1 ab.2)))

theorem relativeEntropy_product_reference (p : α × β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hp : IsProbability p) (_hu : IsProbability u) (_hv : IsProbability v)
    (hsu : SupportedBy (firstMarginal p) u) (hsv : SupportedBy (secondMarginal p) v) :
    relativeEntropy p (product u v) =
      relativeEntropy p (product (firstMarginal p) (secondMarginal p)) +
        relativeEntropy (firstMarginal p) u + relativeEntropy (secondMarginal p) v := by
  have hpoint : ∀ ab : α × β, p ab * Real.log (p ab / product u v ab) =
      p ab * Real.log (p ab / product (firstMarginal p) (secondMarginal p) ab) +
      p ab * Real.log (firstMarginal p ab.1 / u ab.1) +
      p ab * Real.log (secondMarginal p ab.2 / v ab.2) := by
    intro ab
    by_cases hzero : p ab = 0
    · simp [hzero]
    have hpos : 0 < p ab := lt_of_le_of_ne (hp.1 ab) (Ne.symm hzero)
    have hleft := ne_of_gt (hpos.trans_le (point_le_firstMarginal p hp ab.1 ab.2))
    have hright := ne_of_gt (hpos.trans_le (point_le_secondMarginal p hp ab.1 ab.2))
    have hune := hsu ab.1 hleft
    have hvne := hsv ab.2 hright
    simp only [product, Real.log_div hzero (mul_ne_zero hune hvne),
      Real.log_div hzero (mul_ne_zero hleft hright), Real.log_mul hune hvne,
      Real.log_mul hleft hright, Real.log_div hleft hune, Real.log_div hright hvne]
    ring
  have hleftSum : (∑ ab : α × β, p ab * Real.log (firstMarginal p ab.1 / u ab.1)) =
      relativeEntropy (firstMarginal p) u := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_mul, relativeEntropy, firstMarginal]
  have hrightSum : (∑ ab : α × β, p ab * Real.log (secondMarginal p ab.2 / v ab.2)) =
      relativeEntropy (secondMarginal p) v := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.sum_mul, relativeEntropy, secondMarginal]
  unfold relativeEntropy
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hleftSum, hrightSum]
  rfl

theorem marginal_relativeEntropy_sum_le (p : α × β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hp : IsProbability p) (hu : IsProbability u) (hv : IsProbability v)
    (hsu : SupportedBy (firstMarginal p) u) (hsv : SupportedBy (secondMarginal p) v) :
    relativeEntropy (firstMarginal p) u + relativeEntropy (secondMarginal p) v ≤
      relativeEntropy p (product u v) := by
  rw [relativeEntropy_product_reference p u v hp hu hv hsu hsv]
  have hn := relativeEntropy_nonneg p (product (firstMarginal p) (secondMarginal p)) hp
    (product_isProbability _ _ (firstMarginal_isProbability p hp)
      (secondMarginal_isProbability p hp)) (joint_supportedBy_product_marginals p hp)
  linarith

end DFVSGames.Foundations.Information


namespace DFVSGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ) (a : α) (b : β) : ℝ := by
  classical
  exact if firstMarginal p a = 0 then fallback b
    else p (a, b) / firstMarginal p a

theorem conditionalKernel_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (a : α) :
    IsProbability (conditionalKernel p fallback a) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · simpa only [IsProbability, conditionalKernel, ite_eq_left hm] using hf
  · constructor
    · intro b
      simp only [conditionalKernel, ite_eq_right hm]
      exact div_nonneg (hp.1 (a, b))
        ((firstMarginal_isProbability p hp).1 a)
    · simp only [conditionalKernel, ite_eq_right hm, div_eq_mul_inv, ← Finset.sum_mul]
      change firstMarginal p a * (firstMarginal p a)⁻¹ = 1
      exact mul_inv_cancel₀ hm

theorem marginal_mul_conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (a : α) (b : β) :
    firstMarginal p a * conditionalKernel p fallback a b = p (a, b) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · have hpoint := point_le_firstMarginal p hp a b
    rw [hm] at hpoint
    have hz : p (a, b) = 0 := le_antisymm hpoint (hp.1 (a, b))
    simp [conditionalKernel, hm, hz]
  · simp only [conditionalKernel, ite_eq_right hm]
    calc
      firstMarginal p a * (p (a, b) / firstMarginal p a)
          = p (a, b) *
              (firstMarginal p a / firstMarginal p a) := by ring
      _ = p (a, b) := by rw [div_self hm, mul_one]

theorem law_of_total_probability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (b : β) :
    (∑ a, firstMarginal p a * conditionalKernel p fallback a b) =
      secondMarginal p b := by
  simp only [marginal_mul_conditionalKernel p fallback hp, secondMarginal]

theorem kernelProduct_isProbability
    (r : α → ℝ) (k : α → β → ℝ)
    (hr : IsProbability r) (hk : ∀ a, IsProbability (k a)) :
    IsProbability (fun ab : α × β => r ab.1 * k ab.1 ab.2) := by
  constructor
  · intro ab
    exact mul_nonneg (hr.1 ab.1) ((hk ab.1).1 ab.2)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
      (hk _).2, mul_one, hr.2]

theorem alternativeInput_conditionalProduct_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ) (r : α → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback)
    (hr : IsProbability r) :
    IsProbability
      (fun ab : α × β => r ab.1 * conditionalKernel p fallback ab.1 ab.2) :=
  kernelProduct_isProbability r (conditionalKernel p fallback) hr
    (conditionalKernel_isProbability p fallback hp hf)

end DFVSGames.Foundations.Information


namespace DFVSGames.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

def totalVariation (μ ν : FiniteDistribution Ω) : ℝ :=
  (∑ x, |μ.weight x - ν.weight x|) / 2

theorem totalVariation_nonnegative (μ ν : FiniteDistribution Ω) :
    0 ≤ μ.totalVariation ν :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem totalVariation_comm (μ ν : FiniteDistribution Ω) :
    μ.totalVariation ν = ν.totalVariation μ := by
  unfold totalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

theorem probability_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event - ν.probability event ≤ μ.totalVariation ν := by
  have pointwise (x : Ω) :
      2 * ((if event x then μ.weight x else 0) -
        (if event x then ν.weight x else 0)) ≤
      |μ.weight x - ν.weight x| + (μ.weight x - ν.weight x) := by
    have h₁ := le_abs_self (μ.weight x - ν.weight x)
    have h₂ := neg_le_abs (μ.weight x - ν.weight x)
    cases event x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have summed := Finset.sum_le_sum (s := Finset.univ) fun x _ => pointwise x
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    μ.normalized, ν.normalized, sub_self, add_zero] at summed
  unfold probability totalVariation
  linarith

theorem probability_abs_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    |μ.probability event - ν.probability event| ≤ μ.totalVariation ν := by
  apply abs_le.mpr
  constructor
  · have h := ν.probability_sub_le_totalVariation μ event
    rw [totalVariation_comm] at h
    linarith
  · exact μ.probability_sub_le_totalVariation ν event

theorem probability_le_add_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event ≤ ν.probability event + μ.totalVariation ν := by
  have h := μ.probability_sub_le_totalVariation ν event
  linarith

end
end DFVSGames.Foundations.Games.FiniteDistribution


namespace DFVSGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

def condition (μ : FiniteDistribution Ω) (given : Ω → Bool)
    (positive : 0 < μ.probability given) : FiniteDistribution Ω where
  weight x := if given x then μ.weight x / μ.probability given else 0
  nonnegative x := by
    split
    · exact div_nonneg (μ.nonnegative x) positive.le
    · exact le_rfl
  normalized := by
    calc
      _ = (∑ x, if given x then μ.weight x else 0) / μ.probability given := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : given x = true <;> simp [hx]
      _ = 1 := div_self (ne_of_gt positive)

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

theorem probability_inter_eq_mul_conditional (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given) :
    μ.probability (fun x => given x && event x) =
      μ.probability given * (μ.condition given positive).probability event := by
  have h := (eq_div_iff (ne_of_gt positive)).mp
    (μ.probability_condition given event positive)
  simpa only [mul_comm] using h.symm

theorem probability_and_le_left (μ : FiniteDistribution Ω) (event event' : Ω → Bool) :
    μ.probability (fun x => event x && event' x) ≤ μ.probability event := by
  apply μ.probability_mono
  intro x hx
  have h : event x = true ∧ event' x = true := by simpa using hx
  exact h.1

theorem probability_and_le_right (μ : FiniteDistribution Ω) (event event' : Ω → Bool) :
    μ.probability (fun x => event x && event' x) ≤ μ.probability event' := by
  apply μ.probability_mono
  intro x hx
  have h : event x = true ∧ event' x = true := by simpa using hx
  exact h.2

theorem probability_and_eq_zero_of_probability_eq_zero (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (zero : μ.probability given = 0) :
    μ.probability (fun x => given x && event x) = 0 := by
  apply le_antisymm
  · exact (μ.probability_and_le_left given event).trans_eq zero
  · exact μ.probability_nonnegative _

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  {n : Nat}

theorem selectedWins_insert (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (coordinate : Fin n) :
    G.selectedWins strategy (insert coordinate selected) =
      fun questions =>
        G.selectedWins strategy selected questions && G.coordinateWin strategy coordinate questions := by
  classical
  funext questions
  apply Bool.eq_iff_iff.mpr
  simp [selectedWins, and_comm]

def selectedSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  (G.repetition n).questions.probability (G.selectedWins strategy selected)

theorem selectedSuccess_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : 0 ≤ G.selectedSuccess strategy selected :=
  (G.repetition n).questions.probability_nonnegative _

theorem selectedSuccess_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : G.selectedSuccess strategy selected ≤ 1 :=
  (G.repetition n).questions.probability_le_one _

@[simp] theorem selectedSuccess_empty (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy ∅ = 1 := by
  have h : G.selectedWins strategy ∅ = fun _ => true :=
    funext (G.selectedWins_empty strategy)
  rw [selectedSuccess, h, FiniteDistribution.probability_true]

theorem selectedSuccess_univ (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy Finset.univ = (G.repetition n).success strategy := by
  rw [selectedSuccess, G.selectedWins_univ]
  rfl

theorem selectedSuccess_antitone (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    Antitone (G.selectedSuccess strategy) := by
  intro selected selected' h
  exact G.selectedWins_mono strategy h

theorem selectedSuccess_insert (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (coordinate : Fin n)
    (positive : 0 < G.selectedSuccess strategy selected) :
    G.selectedSuccess strategy (insert coordinate selected) =
      G.selectedSuccess strategy selected *
        ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
          (G.coordinateWin strategy coordinate) := by
  unfold selectedSuccess
  rw [G.selectedWins_insert]
  exact (G.repetition n).questions.probability_inter_eq_mul_conditional _ _ positive

theorem selectedSuccess_insert_eq_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (coordinate : Fin n)
    (zero : G.selectedSuccess strategy selected = 0) :
    G.selectedSuccess strategy (insert coordinate selected) = 0 := by
  apply le_antisymm
  · exact (G.selectedSuccess_antitone strategy (Finset.subset_insert coordinate selected)).trans_eq zero
  · exact G.selectedSuccess_nonnegative _ _

end Game

end

end DFVSGames.Foundations.Games


namespace DFVSGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem gameLaw_isProbability (μ : Games.FiniteDistribution α) : IsProbability μ.weight :=
  ⟨μ.nonnegative, μ.normalized⟩

def toGameLaw (p : α → ℝ) (hp : IsProbability p) : Games.FiniteDistribution α where
  weight := p
  nonnegative := hp.1
  normalized := hp.2

def gameLawEquiv : Games.FiniteDistribution α ≃ {p : α → ℝ // IsProbability p} where
  toFun μ := ⟨μ.weight, gameLaw_isProbability μ⟩
  invFun p := toGameLaw p.1 p.2
  left_inv μ := by cases μ; rfl
  right_inv p := by cases p; rfl

theorem totalVariation_gameLaw (μ ν : Games.FiniteDistribution α) :
    totalVariation μ.weight ν.weight = μ.totalVariation ν := rfl

noncomputable def gameConditionalKernel (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) : Games.FiniteDistribution β :=
  toGameLaw (conditionalKernel μ.weight fallback.weight a)
    (conditionalKernel_isProbability μ.weight fallback.weight
      (gameLaw_isProbability μ) (gameLaw_isProbability fallback) a)

theorem gameConditionalKernel_recombine (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) (b : β) :
    firstMarginal μ.weight a * (gameConditionalKernel μ fallback a).weight b =
      μ.weight (a, b) :=
  marginal_mul_conditionalKernel μ.weight fallback.weight (gameLaw_isProbability μ) a b

noncomputable def gameConditionalProduct (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (newInput : Games.FiniteDistribution α) :
    Games.FiniteDistribution (α × β) :=
  toGameLaw (fun ab => newInput.weight ab.1 * conditionalKernel μ.weight fallback.weight ab.1 ab.2)
    (alternativeInput_conditionalProduct_isProbability μ.weight fallback.weight newInput.weight
      (gameLaw_isProbability μ) (gameLaw_isProbability fallback) (gameLaw_isProbability newInput))

theorem gameConditionalProduct_weight (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (newInput : Games.FiniteDistribution α)
    (a : α) (b : β) :
    (gameConditionalProduct μ fallback newInput).weight (a, b) =
      newInput.weight a * (gameConditionalKernel μ fallback a).weight b := rfl

theorem gameCondition_weight (μ : Games.FiniteDistribution α) (event : α → Bool)
    (positive : 0 < μ.probability event) :
    (μ.condition event positive).weight =
      posterior μ.weight (fun a => if event a then 1 else 0) (μ.probability event) := by
  funext a
  cases he : event a <;> simp [Games.FiniteDistribution.condition, posterior, he]

theorem gameCondition_relativeEntropy_le (μ : Games.FiniteDistribution α) (event : α → Bool)
    (positive : 0 < μ.probability event) :
    relativeEntropy (μ.condition event positive).weight μ.weight ≤
      Real.log (1 / μ.probability event) := by
  rw [gameCondition_weight]
  apply posterior_relativeEntropy_le μ.weight (fun a => if event a then 1 else 0)
    (gameLaw_isProbability μ)
  · intro a
    cases event a <;> norm_num
  · intro a
    cases event a <;> norm_num
  · exact positive
  · unfold Games.FiniteDistribution.probability
    apply Finset.sum_congr rfl
    intro a _
    cases event a <;> simp

end DFVSGames.Foundations.Information


namespace DFVSGames.Foundations.Repetition

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
  convert h using 1 ; ring

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

end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_joint_common_weights (w : α → ℝ) (p q : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    totalVariation (fun ab : α × β => w ab.1 * p ab.1 ab.2)
      (fun ab : α × β => w ab.1 * q ab.1 ab.2) =
        ∑ a, w a * totalVariation (p a) (q a) := by
  have hpoint : ∀ a b, |w a * p a b - w a * q a b| = w a * |p a b - q a b| := by
    intro a b
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw a)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem totalVariation_joint_common_kernel (p q : α → ℝ) (k : α → β → ℝ)
    (hk : ∀ a, IsProbability (k a)) :
    totalVariation (fun ab : α × β => p ab.1 * k ab.1 ab.2)
      (fun ab : α × β => q ab.1 * k ab.1 ab.2) = totalVariation p q := by
  have hpoint : ∀ a b, |p a * k a b - q a * k a b| = |p a - q a| * k a b := by
    intro a b
    rw [← sub_mul, abs_mul, abs_of_nonneg ((hk a).1 b)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    (hk _).2, mul_one]

theorem totalVariation_condition_le (p q : α → ℝ) (event : α → Prop)
    [DecidablePred event] {c : ℝ} (hc : 0 < c) :
    totalVariation (fun a => if event a then p a / c else 0)
      (fun a => if event a then q a / c else 0) ≤ totalVariation p q / c := by
  have hpoint : ∀ a, |(if event a then p a / c else 0) -
      (if event a then q a / c else 0)| ≤ |p a - q a| / c := by
    intro a
    by_cases he : event a
    · simp only [ite_eq_left he, ← sub_div, abs_div, abs_of_pos hc, le_refl]
    · simp only [ite_eq_right he, sub_self, abs_zero]
      exact div_nonneg (abs_nonneg _) hc.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [div_eq_mul_inv, ← Finset.sum_mul] at hsum
  have hd := div_le_div_of_nonneg_right hsum (show (0 : ℝ) ≤ 2 by norm_num)
  have hreorder : ((∑ a, |p a - q a|) * c⁻¹) / 2 =
      ((∑ a, |p a - q a|) / 2) / c := by ring
  rw [hreorder] at hd
  simpa only [totalVariation, div_eq_mul_inv] using hd

theorem weighted_coordinate_sum_sq_le
    (w : α → ℝ) (d : α → β → ℝ) (C : α → ℝ)
    (hw : IsProbability w)
    (hbudget : ∀ a, w a * (∑ b, d a b ^ 2) ≤ w a * C a) :
    (∑ b, ∑ a, w a * d a b)^2 ≤
      (Fintype.card β : ℝ) * (∑ a, w a * C a) := by
  have hv := Finset.sum_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset β)) =>
      weighted_sum_sq_le w (fun a => d a b) hw)
  have he :
      (∑ b, ∑ a, w a * d a b ^ 2) =
        ∑ a, w a * (∑ b, d a b ^ 2) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [he] at hv
  have hb := Finset.sum_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset α)) => hbudget a)
  have hs := hv.trans hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset β)
    (fun b => ∑ a, w a * d a b) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  calc
    (∑ b, ∑ a, w a * d a b)^2
        ≤ (∑ b, (∑ a, w a * d a b)^2) *
            (Fintype.card β : ℝ) := hcs
    _ = (Fintype.card β : ℝ) *
          (∑ b, (∑ a, w a * d a b)^2) := mul_comm _ _
    _ ≤ (Fintype.card β : ℝ) * (∑ a, w a * C a) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

end DFVSGames.Foundations.Information


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Information

private theorem min_half_formula_inline_Overlap (x y : ℝ) :
    min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem sum_min_one_sub_tv {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ) (hp : IsProbability p) (hq : IsProbability q) :
    (∑ z, min (p z) (q z)) = 1 - totalVariation p q := by
  classical
  simp_rw [min_half_formula_inline_Overlap]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.2, hq.2, totalVariation]
  ring

private theorem discount_le_self_inline_Overlap {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c / (1 + t) ≤ c := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).2
  nlinarith [mul_nonneg hc ht]

private theorem discount_loss_le_mul_inline_Overlap {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c - c / (1 + t) ≤ c * t := by
  have hd : 0 < 1 + t := by linarith
  have hid : c - c / (1 + t) = c * t / (1 + t) := by
    field_simp [hd.ne']
    ring
  rw [hid]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg (mul_nonneg hc ht) ht]

noncomputable def discountedCommonMass {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (t : X → ℝ) : ℝ :=
  ∑ z, min (p z) (min (a z) (b z)) / (1 + t z.1)

theorem discounted_common_mass_bounds {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (μ t : X → ℝ)
    (hp : IsProbability p) (ha : IsProbability a) (hb : IsProbability b)
    (ht : ∀ x, 0 ≤ t x)
    (hrow : ∀ x, (∑ s, a (x, s)) = μ x)
    (htv : (∑ x, μ x * t x) = totalVariation a b) :
    1 - 2 * totalVariation p a - 2 * totalVariation p b ≤ discountedCommonMass p a b t ∧
      discountedCommonMass p a b t ≤ 1 := by
  classical
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have hC0 : ∀ z, 0 ≤ C z := by
    intro z
    exact le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
  have hCp : ∀ z, C z ≤ p z := by
    intro z
    exact min_le_left _ _
  have hCa : ∀ z, C z ≤ a z := by
    intro z
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmass : 1 - totalVariation p a - totalVariation p b ≤ ∑ z, C z := by
    have hpoint : ∀ z, min (p z) (a z) + min (p z) (b z) - p z ≤ C z := by
      intro z
      dsimp [C]
      refine le_min ?_ (le_min ?_ ?_)
      · linarith [min_le_left (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (b z), min_le_left (p z) (a z)]
    have hsum := Finset.sum_le_sum
      (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
    rw [sum_min_one_sub_tv p a hp ha, sum_min_one_sub_tv p b hp hb, hp.2] at hsum
    linarith
  have hrowC : ∀ x, (∑ s, C (x, s)) ≤ μ x := by
    intro x
    calc
      (∑ s, C (x, s)) ≤ ∑ s, a (x, s) := Finset.sum_le_sum (fun s _ => hCa (x, s))
      _ = μ x := hrow x
  have hweighted : (∑ z, C z * t z.1) ≤ totalVariation a b := by
    rw [← htv, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro x _
    change (∑ s, C (x, s) * t x) ≤ μ x * t x
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrowC x) (ht x)
  have hloss : (∑ z, C z) - discountedCommonMass p a b t ≤ ∑ z, C z * t z.1 := by
    change (∑ z, C z) - (∑ z, C z / (1 + t z.1)) ≤ ∑ z, C z * t z.1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun z _ => discount_loss_le_mul_inline_Overlap (hC0 z) (ht z.1))
  have htriangle : totalVariation a b ≤ totalVariation p a + totalVariation p b := by
    have h := totalVariation_triangle a p b
    rw [totalVariation_symm a p] at h
    exact h
  have hupper : discountedCommonMass p a b t ≤ 1 := by
    change (∑ z, C z / (1 + t z.1)) ≤ 1
    calc
      _ ≤ ∑ z, p z := Finset.sum_le_sum
        (fun z _ => (discount_le_self_inline_Overlap (hC0 z) (ht z.1)).trans (hCp z))
      _ = 1 := hp.2
  exact ⟨by linarith, hupper⟩

noncomputable def diagonalWeights {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) : X × S × S → ℝ := by
  classical
  exact fun z => if z.2.1 = z.2.2 then p (z.1, z.2.1) else 0

theorem diagonalWeights_isProbability {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (hp : IsProbability p) : IsProbability (diagonalWeights p) := by
  classical
  constructor
  · intro z
    dsimp [diagonalWeights]
    split
    · exact hp.1 _
    · exact le_rfl
  · simpa [diagonalWeights, Fintype.sum_prod_type] using hp.2

theorem diagonal_overlap_identity {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (sim : X × S × S → ℝ)
    (hp : IsProbability p) (hsim : IsProbability sim) :
    totalVariation sim (diagonalWeights p) =
      1 - ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
  classical
  have h := sum_min_one_sub_tv sim (diagonalWeights p) hsim (diagonalWeights_isProbability p hp)
  have heq : (∑ z, min (sim z) (diagonalWeights p z)) =
      ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
    simp only [Fintype.sum_prod_type, diagonalWeights]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro s _
    have hpoint : ∀ s', min (sim (x, s, s')) (if s = s' then p (x, s) else 0) =
        if s = s' then min (p (x, s)) (sim (x, s, s')) else 0 := by
      intro s'
      by_cases he : s = s'
      · simp [he, min_comm]
      · simp [he, min_eq_right (hsim.1 (x, s, s'))]
    simp only [hpoint]
    simp
  rw [heq] at h
  linarith

theorem diagonal_sampler_totalVariation_le {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (μ : X → ℝ) (L R : X → S → ℝ)
    (sim : X × S × S → ℝ) (hp : IsProbability p) (hμ : IsProbability μ)
    (hL : ∀ x, IsProbability (L x)) (hR : ∀ x, IsProbability (R x))
    (hsim : IsProbability sim) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hdiag : ∀ x s, μ x * min (L x s) (R x s) /
      (1 + totalVariation (L x) (R x)) * (1 - τ) ≤ sim (x, s, s)) :
    totalVariation sim (diagonalWeights p) ≤
      2 * totalVariation p (fun z => μ z.1 * L z.1 z.2) +
      2 * totalVariation p (fun z => μ z.1 * R z.1 z.2) + τ := by
  classical
  let a : X × S → ℝ := fun z => μ z.1 * L z.1 z.2
  let b : X × S → ℝ := fun z => μ z.1 * R z.1 z.2
  let t : X → ℝ := fun x => totalVariation (L x) (R x)
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have ha : IsProbability a := kernelProduct_isProbability μ L hμ hL
  have hb : IsProbability b := kernelProduct_isProbability μ R hμ hR
  have ht : ∀ x, 0 ≤ t x := fun x => totalVariation_nonneg (L x) (R x)
  have hrow : ∀ x, (∑ s, a (x, s)) = μ x := by
    intro x
    simp only [a, ← Finset.mul_sum, (hL x).2, mul_one]
  have htv : (∑ x, μ x * t x) = totalVariation a b :=
    (totalVariation_joint_common_weights μ L R hμ.1).symm
  obtain ⟨hBlower, hBupper⟩ := discounted_common_mass_bounds p a b μ t hp ha hb ht hrow htv
  have hpoint : ∀ z : X × S,
      (1 - τ) * (C z / (1 + t z.1)) ≤ min (p z) (sim (z.1, z.2, z.2)) := by
    intro z
    have hden : 0 < 1 + t z.1 := by linarith [ht z.1]
    have hC0 : 0 ≤ C z := le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
    have hCp : C z ≤ p z := min_le_left _ _
    have hdisc0 : 0 ≤ C z / (1 + t z.1) := div_nonneg hC0 hden.le
    have hmin : min (a z) (b z) = μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      dsimp [a, b]
      rcases le_total (L z.1 z.2) (R z.1 z.2) with h | h
      · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
      · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
    have hCmin : C z ≤ μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      rw [← hmin]
      exact min_le_right _ _
    apply le_min
    · calc
        _ ≤ 1 * (C z / (1 + t z.1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hdisc0
        _ ≤ C z := by simpa using discount_le_self_inline_Overlap hC0 (ht z.1)
        _ ≤ p z := hCp
    · have hd := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hCmin hden.le) (by linarith : 0 ≤ 1 - τ)
      calc
        _ ≤ (1 - τ) * (μ z.1 * min (L z.1 z.2) (R z.1 z.2) / (1 + t z.1)) := hd
        _ ≤ sim (z.1, z.2, z.2) := by
          simpa only [t, mul_comm] using hdiag z.1 z.2
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
  rw [← Finset.mul_sum] at hsum
  change (1 - τ) * discountedCommonMass p a b t ≤ _ at hsum
  rw [diagonal_overlap_identity p sim hp hsim]
  have hτB := mul_le_mul_of_nonneg_left hBupper hτ0
  change 1 - _ ≤ 2 * totalVariation p a + 2 * totalVariation p b + τ
  nlinarith

end DFVSGames.Foundations.Repetition

end OAI
