import OAI.Combinatorics.Ryser.Probability.Finite
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.FiniteLaw

lemma expectation_mul_left_real {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    p.expectation (fun a => c * f a) = c * p.expectation f := by
  classical
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := (le_abs_self (Real.exp x - 1 - x)).trans
    (Real.abs_exp_sub_one_sub_id_le hx)
  linarith

lemma expectation_exp_le_of_mean_zero {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (z : Ω → ℝ) (M v θ : ℝ)
    (hz : p.expectation z = 0)
    (hbound : ∀ a, |z a| ≤ M)
    (hsecond : p.expectation (fun a => (z a) ^ 2) ≤ v)
    (hθ : |θ| * M ≤ 1) :
    p.expectation (fun a => Real.exp (θ * z a)) ≤
      Real.exp (θ ^ 2 * v) := by
  classical
  have hpoint (a : Ω) :
      Real.exp (θ * z a) ≤ 1 + θ * z a + θ ^ 2 * (z a) ^ 2 := by
    have habs : |θ * z a| ≤ 1 := calc
      |θ * z a| = |θ| * |z a| := abs_mul _ _
      _ ≤ |θ| * M := mul_le_mul_of_nonneg_left (hbound a) (abs_nonneg θ)
      _ ≤ 1 := hθ
    have he := exp_le_one_add_add_sq habs
    nlinarith [he]
  have hlin :
      (∑ a, p.weight a * (θ * z a)) = θ * p.expectation z := by
    exact expectation_mul_left_real p θ z
  have hquad :
      (∑ a, p.weight a * (θ ^ 2 * (z a) ^ 2)) =
        θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
    exact expectation_mul_left_real p (θ ^ 2) (fun a => (z a) ^ 2)
  calc
    p.expectation (fun a => Real.exp (θ * z a)) ≤
        p.expectation (fun a => 1 + θ * z a + θ ^ 2 * (z a) ^ 2) := by
      unfold expectation
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hpoint a) (p.nonneg a)
    _ = 1 + θ * p.expectation z +
        θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
      change (∑ a, p.weight a * (1 + θ * z a + θ ^ 2 * (z a) ^ 2)) = _
      simp only [mul_add, mul_one, Finset.sum_add_distrib]
      rw [p.total, hlin, hquad]
    _ = 1 + θ ^ 2 * p.expectation (fun a => (z a) ^ 2) := by
      rw [hz]
      ring
    _ ≤ 1 + θ ^ 2 * v :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsecond (sq_nonneg θ))
    _ ≤ Real.exp (θ ^ 2 * v) := by
      simpa only [add_comm] using Real.add_one_le_exp (θ ^ 2 * v)

lemma iterated_centered_mgf_le
    {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (q : A → FiniteLaw B)
    (f : A → B → ℝ) (head : A → ℝ)
    (center θ v V : ℝ)
    (hhead : p.expectation (fun a => Real.exp (θ * (head a - center))) ≤
      Real.exp (θ ^ 2 * v))
    (htail : ∀ a, (q a).expectation
        (fun b => Real.exp (θ * (f a b - head a))) ≤ Real.exp (θ ^ 2 * V)) :
    p.expectation (fun a => (q a).expectation
      (fun b => Real.exp (θ * (f a b - center)))) ≤
        Real.exp (θ ^ 2 * (v + V)) := by
  classical
  have hsplit (a : A) :
      (q a).expectation (fun b => Real.exp (θ * (f a b - center))) =
        Real.exp (θ * (head a - center)) *
          (q a).expectation (fun b => Real.exp (θ * (f a b - head a))) := by
    rw [← expectation_mul_left_real]
    congr 1
    funext b
    rw [← Real.exp_add]
    congr 1
    ring
  have hinner (a : A) :
      (q a).expectation (fun b => Real.exp (θ * (f a b - center))) ≤
        Real.exp (θ ^ 2 * V) * Real.exp (θ * (head a - center)) := by
    rw [hsplit]
    have h := mul_le_mul_of_nonneg_left (htail a)
      (Real.exp_pos (θ * (head a - center))).le
    simpa only [mul_comm] using h
  calc
    p.expectation (fun a => (q a).expectation
        (fun b => Real.exp (θ * (f a b - center)))) ≤
        p.expectation (fun a =>
          Real.exp (θ ^ 2 * V) * Real.exp (θ * (head a - center))) := by
      unfold expectation
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hinner a) (p.nonneg a)
    _ = Real.exp (θ ^ 2 * V) *
        p.expectation (fun a => Real.exp (θ * (head a - center))) :=
      expectation_mul_left_real p _ _
    _ ≤ Real.exp (θ ^ 2 * V) * Real.exp (θ ^ 2 * v) :=
      mul_le_mul_of_nonneg_left hhead (Real.exp_pos _).le
    _ = Real.exp (θ ^ 2 * (v + V)) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma chernoff_upper {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u θ : ℝ) (hθ : 0 ≤ θ) :
    p.prob (fun a => u ≤ f a) ≤
      Real.exp (-θ * u) * p.expectation (fun a => Real.exp (θ * f a)) := by
  classical
  unfold prob expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  by_cases huf : u ≤ f a
  · simp only [ite_eq_left huf]
    have he : 1 ≤ Real.exp (-θ * u) * Real.exp (θ * f a) := calc
      1 = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (-θ * u + θ * f a) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hθ (sub_nonneg.mpr huf)]
      _ = Real.exp (-θ * u) * Real.exp (θ * f a) := Real.exp_add _ _
    calc
      p.weight a = p.weight a * 1 := by ring
      _ ≤ p.weight a * (Real.exp (-θ * u) * Real.exp (θ * f a)) :=
        mul_le_mul_of_nonneg_left he (p.nonneg a)
      _ = Real.exp (-θ * u) * (p.weight a * Real.exp (θ * f a)) := by ring
  · simp only [ite_eq_right huf]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (p.nonneg a) (Real.exp_pos _).le)

lemma chernoff_upper_of_mgf {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u θ V : ℝ)
    (hθ : 0 ≤ θ)
    (hmgf : p.expectation (fun a => Real.exp (θ * f a)) ≤
      Real.exp (θ ^ 2 * V)) :
    p.prob (fun a => u ≤ f a) ≤ Real.exp (θ ^ 2 * V - θ * u) := by
  calc
    p.prob (fun a => u ≤ f a) ≤
        Real.exp (-θ * u) * p.expectation (fun a => Real.exp (θ * f a)) :=
      chernoff_upper p f u θ hθ
    _ ≤ Real.exp (-θ * u) * Real.exp (θ ^ 2 * V) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (θ ^ 2 * V - θ * u) := by
      rw [← Real.exp_add]
      congr 1
      ring

lemma bernstein_scalar_optimization
    (M V u P : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 / M →
      P ≤ Real.exp (t ^ 2 * V - t * u)) :
    P ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  by_cases hcut : u / (2 * V) ≤ 1 / M
  · have ht : 0 < u / (2 * V) :=
      div_pos hu (mul_pos (by norm_num) hV)
    have hexp :
        (u / (2 * V)) ^ 2 * V - (u / (2 * V)) * u =
          -(1 / 4 : ℝ) * (u ^ 2 / V) := by
      field_simp [ne_of_gt hV]; ring
    calc
      P ≤ Real.exp ((u / (2 * V)) ^ 2 * V - (u / (2 * V)) * u) :=
        h _ ht hcut
      _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
        apply Real.exp_le_exp.mpr
        rw [hexp]
        nlinarith [min_le_left (u ^ 2 / V) (u / M)]
  · have hcross : 2 * V < u * M := by
      have ht : 1 / M < u / (2 * V) := lt_of_not_ge hcut
      have ht' :=
        (div_lt_div_iff₀ hM (mul_pos (by norm_num) hV)).mp ht
      simpa using ht'
    have hnum : V - u * M ≤ -(u * M) / 4 := by
      nlinarith [mul_pos hu hM]
    have hexp :
        (1 / M) ^ 2 * V - (1 / M) * u ≤
          -(1 / 4 : ℝ) * (u / M) := by
      calc
        (1 / M) ^ 2 * V - (1 / M) * u =
            (V - u * M) / M ^ 2 := by
          field_simp [ne_of_gt hM]
        _ ≤ (-(u * M) / 4) / M ^ 2 :=
          div_le_div_of_nonneg_right hnum (sq_nonneg M)
        _ = -(1 / 4 : ℝ) * (u / M) := by
          field_simp [ne_of_gt hM]
    calc
      P ≤ Real.exp ((1 / M) ^ 2 * V - (1 / M) * u) :=
        h _ (div_pos (by norm_num) hM) le_rfl
      _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
        apply Real.exp_le_exp.mpr
        have hmin :
            -(1 / 4 : ℝ) * (u / M) ≤
              -(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M) := by
          nlinarith [min_le_right (u ^ 2 / V) (u / M)]
        exact hexp.trans hmin

lemma prob_abs_ge_le_add {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (u : ℝ) :
    p.prob (fun a => u ≤ |f a|) ≤
      p.prob (fun a => u ≤ f a) + p.prob (fun a => u ≤ -f a) := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  change (if u ≤ |f a| then p.weight a else 0) ≤
    (if u ≤ f a then p.weight a else 0) + (if u ≤ -f a then p.weight a else 0)
  by_cases hs : 0 ≤ f a
  · rw [abs_of_nonneg hs]
    split_ifs <;> linarith [p.nonneg a]
  · rw [abs_of_nonpos (le_of_not_ge hs)]
    split_ifs <;> linarith [p.nonneg a]

lemma bernstein_abs_tail_of_mgf {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hmgf : ∀ θ : ℝ, |θ| * M ≤ 1 →
      p.expectation (fun a => Real.exp (θ * f a)) ≤
        Real.exp (θ ^ 2 * V)) :
    p.prob (fun a => u ≤ |f a|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  have upper : p.prob (fun a => u ≤ f a) ≤
      Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
    apply bernstein_scalar_optimization M V u _ hM hV hu
    intro θ hθ hθM
    have hadm : |θ| * M ≤ 1 := by
      rw [abs_of_pos hθ]
      exact (le_div_iff₀ hM).mp hθM
    exact chernoff_upper_of_mgf p f u θ V hθ.le (hmgf θ hadm)
  have lower : p.prob (fun a => u ≤ -f a) ≤
      Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
    apply bernstein_scalar_optimization M V u _ hM hV hu
    intro θ hθ hθM
    have hadm : |θ| * M ≤ 1 := by
      rw [abs_of_pos hθ]
      exact (le_div_iff₀ hM).mp hθM
    have hadmneg : |-θ| * M ≤ 1 := by
      simpa only [abs_neg] using hadm
    have hneg : p.expectation (fun a => Real.exp (θ * (-f a))) ≤
        Real.exp (θ ^ 2 * V) := by
      simpa only [neg_mul, mul_neg, neg_sq] using hmgf (-θ) hadmneg
    exact chernoff_upper_of_mgf p (fun a => -f a) u θ V hθ.le hneg
  calc
    p.prob (fun a => u ≤ |f a|) ≤
        p.prob (fun a => u ≤ f a) + p.prob (fun a => u ≤ -f a) :=
      prob_abs_ge_le_add p f u
    _ ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) +
        Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) :=
      add_le_add upper lower
    _ = 2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by ring

end RyserCoveringCounterexample.FiniteLaw

end OAI
