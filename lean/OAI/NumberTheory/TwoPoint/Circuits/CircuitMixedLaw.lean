import OAI.NumberTheory.TwoPoint.Circuits.CircuitGateApproximation

namespace OAI

/-! The half-uniform input law in Braverman's proof. Small exceptional
probability for this law bounds both the uniform and supplied probabilities. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def cubeDensityLaw {n : ℕ} (g : BooleanCube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1) : FiniteLaw (BooleanCube n) where
  weight x := g x / Fintype.card (BooleanCube n)
  nonneg x := div_nonneg (hg x) (Nat.cast_nonneg _)
  total := by simpa only [← sum_div, cubeAverage] using hmean

lemma cubeDensityLaw_average {n : ℕ} (g : BooleanCube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1) (f : BooleanCube n → ℝ) :
    (cubeDensityLaw g hg hmean).average f = cubeAverage (fun x => g x * f x) := by
  unfold FiniteLaw.average cubeDensityLaw cubeAverage
  rw [sum_div]
  apply sum_congr rfl
  intro x _
  ring

lemma half_uniform_density_mean {n : ℕ} (g : BooleanCube n → ℝ)
    (hmean : cubeAverage g = 1) :
    cubeAverage (fun x => (g x + 1) / 2) = 1 := by
  have heq : (fun x => (g x + 1) / 2) = fun x => (1 / 2 : ℝ) * (g x + 1) := by
    funext x
    ring
  rw [heq, cubeAverage_mul_const, cubeAverage_add, hmean, cubeAverage_const]
  norm_num

noncomputable def mixedCubeLaw {n : ℕ} (g : BooleanCube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1) : FiniteLaw (BooleanCube n) :=
  cubeDensityLaw (fun x => (g x + 1) / 2) (fun x => by have hx := hg x; positivity)
    (half_uniform_density_mean g hmean)

lemma mixedCubeLaw_probability {n : ℕ} (g : BooleanCube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1) (E : BooleanCube n → Prop) :
    (mixedCubeLaw g hg hmean).probability E =
      ((cubeDensityLaw g hg hmean).probability E +
        cubeAverage (fun x => if E x then (1 : ℝ) else 0)) / 2 := by
  unfold mixedCubeLaw FiniteLaw.probability
  rw [cubeDensityLaw_average, cubeDensityLaw_average]
  have heq : (fun x => (g x + 1) / 2 * (if E x then (1 : ℝ) else 0)) =
      fun x => (1 / 2 : ℝ) *
        (g x * (if E x then (1 : ℝ) else 0) + (if E x then (1 : ℝ) else 0)) := by
    funext x
    ring
  rw [heq, cubeAverage_mul_const, cubeAverage_add]
  ring

theorem mixedCubeLaw_exception_bounds {n : ℕ} (g : BooleanCube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1) (E : BooleanCube n → Prop)
    {δ : ℝ} (hE : (mixedCubeLaw g hg hmean).probability E ≤ δ) :
    (cubeDensityLaw g hg hmean).probability E ≤ 2 * δ ∧
      cubeAverage (fun x => if E x then (1 : ℝ) else 0) ≤ 2 * δ := by
  rw [mixedCubeLaw_probability] at hE
  have hμ := (cubeDensityLaw g hg hmean).probability_nonneg E
  have hU : 0 ≤ cubeAverage (fun x => if E x then (1 : ℝ) else 0) := by
    calc
      0 = cubeAverage (fun _ : BooleanCube n => (0 : ℝ)) := by simp
      _ ≤ _ := cubeAverage_mono (fun x => by split_ifs <;> norm_num)
  constructor <;> linarith

end TwoPointCorrelations

end OAI
