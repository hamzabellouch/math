import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

/-!
Finite total-variation operations used by the dependency-breaking argument.
All statements concern the displayed real weight functions. In particular,
conditioning rescales actual restricted weights, and kernels act by finite sums.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

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

/-- The actual weights obtained by restricting to an event and normalizing. -/
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

/-- Conditioning two laws on the same event of equal positive mass costs at
most the inverse mass. The algebraic estimate itself needs no normalization. -/
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

/-- Appending the same conditional kernel preserves total variation exactly. -/
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

/-- Applying a finite stochastic kernel, forgetting its input. -/
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

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
