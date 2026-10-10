import OAI.NumberTheory.TwoPoint.Bounds.PaddingSelectionLaw
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! Exact exponential moments and elementary upper tails for the finite
independent Boolean laws used by the two prime-degree deletions. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma FiniteLaw.probability_lt_exp_bound {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (Z : A → ℝ) (a t : ℝ) (ht : 0 ≤ t) :
    μ.probability (fun x => a < Z x) ≤
      Real.exp (-t * a) * μ.average (fun x => Real.exp (t * Z x)) := by
  calc
    _ ≤ μ.average (fun x => Real.exp (t * Z x) * Real.exp (-t * a)) := by
      apply μ.average_mono
      intro x
      by_cases hx : a < Z x
      · rw [ite_eq_left hx, ← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith
      · rw [ite_eq_right hx]
        positivity
    _ = _ := by rw [μ.average_mul_const]; ring

noncomputable def booleanCount {ι : Type*} [Fintype ι] (a : ι → Bool) : ℝ :=
  ∑ i, if a i then 1 else 0

lemma booleanCount_eq_card {ι : Type*} [Fintype ι] (a : ι → Bool) :
    booleanCount a = ((univ.filter (fun i => a i = true)).card : ℝ) := by
  exact sum_boole (fun i => a i = true) univ

lemma booleanLaw_exp_average (q t : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (booleanLaw q hq0 hq1).average (fun b => Real.exp (t * (if b then 1 else 0))) =
      1 + q * (Real.exp t - 1) := by
  simp [FiniteLaw.average, booleanLaw]
  ring

lemma independent_boolean_exp_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (t : ℝ) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => Real.exp (t * booleanCount a)) =
        ∏ i, (1 + q i * (Real.exp t - 1)) := by
  have he (a : ι → Bool) : Real.exp (t * booleanCount a) =
      ∏ i, Real.exp (t * (if a i then 1 else 0)) := by
    rw [booleanCount, mul_sum, Real.exp_sum]
  simp_rw [he]
  rw [FiniteLaw.independent_average_product
    (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
    (fun _ b => Real.exp (t * (if b then 1 else 0)))]
  simp only [booleanLaw_exp_average]

lemma independent_boolean_exp_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (t M : ℝ) (ht : 0 ≤ t) (hM : (∑ i, q i) ≤ M) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => Real.exp (t * booleanCount a)) ≤ Real.exp ((Real.exp t - 1) * M) := by
  rw [independent_boolean_exp_average]
  have hu : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht)
  calc
    _ ≤ ∏ i, Real.exp (q i * (Real.exp t - 1)) := by
      apply prod_le_prod₀
      · intro i _
        exact add_nonneg zero_le_one (mul_nonneg (hq0 i) hu)
      · intro i _
        simpa only [add_comm] using Real.add_one_le_exp (q i * (Real.exp t - 1))
    _ = Real.exp ((∑ i, q i) * (Real.exp t - 1)) := by
      rw [sum_mul, Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- The entire bound is a finite product identity followed by exponential
Markov; no probability theorem is assumed. -/
theorem independent_boolean_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (t M a : ℝ) (ht : 0 ≤ t) (hM : (∑ i, q i) ≤ M) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).probability
      (fun b => a < booleanCount b) ≤
        Real.exp ((Real.exp t - 1) * M - t * a) := by
  apply (FiniteLaw.probability_lt_exp_bound _ _ a t ht).trans
  calc
    _ ≤ Real.exp (-t * a) * Real.exp ((Real.exp t - 1) * M) :=
      mul_le_mul_of_nonneg_left (independent_boolean_exp_bound q hq0 hq1 t M ht hM)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end TwoPointCorrelations

end OAI
