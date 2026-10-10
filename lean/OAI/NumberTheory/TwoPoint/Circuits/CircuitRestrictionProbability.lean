import OAI.NumberTheory.TwoPoint.Circuits.CircuitBernoulli
import OAI.NumberTheory.TwoPoint.Bounds.PrimeRowSecondMoment

namespace OAI

/-! A finite second-moment lower-tail bound for the live coordinates of a
random restriction. It is used to transfer high-degree Fourier mass. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma FiniteLaw.probability_mul_le_average {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (E : α → Prop) (f : α → ℝ) (a : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hE : ∀ x, E x → a ≤ f x) :
    a * μ.probability E ≤ μ.average f := by
  calc
    _ = μ.average (fun x => if E x then a else 0) := by
      unfold FiniteLaw.probability FiniteLaw.average
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      by_cases hx : E x <;> simp [hx]
      ring
    _ ≤ _ := μ.average_mono (fun x => by by_cases hx : E x <;> simp [hx, hf x, hE x])

lemma independent_boolean_variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun b => (booleanCount b - ∑ i, q i) ^ 2) ≤ ∑ i, q i := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  let V := ∑ i, q i
  have hm : μ.average booleanCount = V := independent_boolean_count_average q hq0 hq1
  have hs : μ.average (fun b => (booleanCount b) ^ 2) ≤ V ^ 2 + V :=
    independent_boolean_count_square q hq0 hq1
  have he (b : ι → Bool) : (booleanCount b - V) ^ 2 =
      (booleanCount b) ^ 2 + booleanCount b * (-2 * V) + V ^ 2 := by ring
  change μ.average (fun b => (booleanCount b - V) ^ 2) ≤ V
  simp_rw [he]
  rw [μ.average_add, μ.average_add, μ.average_mul_const, μ.average_const, hm]
  nlinarith

theorem independent_boolean_lower_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (a : ℝ) (ha : 2 * a ≤ ∑ i, q i) (hlarge : 8 ≤ ∑ i, q i) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).probability
      (fun b => booleanCount b ≤ a) ≤ 1 / 2 := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  let V := ∑ i, q i
  have hV : 0 < V := by dsimp [V]; linarith
  have hp : ∀ b : ι → Bool, booleanCount b ≤ a →
      2 * V ≤ (booleanCount b - V) ^ 2 := by
    intro b hb
    have h1 : 0 ≤ V / 2 - booleanCount b := by dsimp [V]; linarith
    have h2 : 0 ≤ 3 * V / 2 - booleanCount b := by dsimp [V]; linarith
    have hh := mul_nonneg h1 h2
    have hv := mul_nonneg hV.le (show 0 ≤ V - 8 by dsimp [V]; linarith)
    nlinarith
  have hm := μ.probability_mul_le_average (fun b => booleanCount b ≤ a)
    (fun b => (booleanCount b - V) ^ 2) (2 * V) (fun _ => sq_nonneg _) hp
  have hv := independent_boolean_variance q hq0 hq1
  change μ.average (fun b => (booleanCount b - V) ^ 2) ≤ V at hv
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * V by positivity)).mp
  calc
    2 * V * μ.probability (fun b => booleanCount b ≤ a) ≤ V := hm.trans hv
    _ = 2 * V * (1 / 2) := by ring

theorem independent_boolean_survival {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (a : ℝ) (ha : 2 * a ≤ ∑ i, q i) (hlarge : 8 ≤ ∑ i, q i) :
    1 / 2 ≤ (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).probability
      (fun b => a < booleanCount b) := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  have h := independent_boolean_lower_tail q hq0 hq1 a ha hlarge
  have hc : μ.probability (fun b => a < booleanCount b) =
      1 - μ.probability (fun b => booleanCount b ≤ a) := by
    simpa only [not_le] using μ.probability_complement (fun b => booleanCount b ≤ a)
  rw [hc]
  linarith

end TwoPointCorrelations

end OAI
