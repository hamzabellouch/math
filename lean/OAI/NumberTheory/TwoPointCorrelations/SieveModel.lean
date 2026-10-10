import OAI.NumberTheory.TwoPointCorrelations.Bonferroni
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pi

namespace OAI

/-! The exact independent model and a generating-function bound for its
Bonferroni remainder. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace FiniteLaw

noncomputable def dependentIndependent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i)) :
    FiniteLaw (∀ i, A i) where
  weight x := ∏ i, (μ i).weight (x i)
  nonneg x := prod_nonneg (fun i _ => (μ i).nonneg (x i))
  total := by
    rw [← Fintype.prod_sum (fun i x => (μ i).weight x)]
    simp only [FiniteLaw.total, prod_const_one]

lemma dependentIndependent_average_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → ℝ) :
    (dependentIndependent μ).average (fun x => ∏ i, f i (x i)) =
      ∏ i, (μ i).average (f i) := by
  simp only [average, dependentIndependent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm

lemma dependentIndependent_probability_all {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) :
    (dependentIndependent μ).probability (fun x => ∀ i, E i (x i)) =
      ∏ i, (μ i).probability (E i) := by
  unfold probability
  calc
    _ = (dependentIndependent μ).average
        (fun x => ∏ i, if E i (x i) then (1 : ℝ) else 0) := by
      congr 1
      funext x
      by_cases hx : ∀ i, E i (x i) <;> simp [Fintype.prod_boole, hx]
    _ = _ := dependentIndependent_average_product μ
      (fun i x => if E i x then (1 : ℝ) else 0)

lemma probability_complement {α : Type*} [Fintype α] (μ : FiniteLaw α) (E : α → Prop) :
    μ.probability (fun x => ¬E x) = 1 - μ.probability E := by
  have hsum : μ.probability E + μ.probability (fun x => ¬E x) = 1 := by
    unfold probability average
    rw [← sum_add_distrib]
    calc
      _ = ∑ x, μ.weight x := by
        apply sum_congr rfl
        intro x _
        by_cases hx : E x <;> simp [hx]
      _ = 1 := μ.total
  linarith

lemma dependentIndependent_intersection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) (S : Finset ι) :
    (dependentIndependent μ).probability (eventIntersection (fun i x => E i (x i)) S) =
      ∏ i ∈ S, (μ i).probability (E i) := by
  have he : eventIntersection (fun i (x : ∀ i, A i) => E i (x i)) S =
      (fun (x : ∀ i, A i) => ∀ i, i ∈ S → E i (x i)) := rfl
  rw [he, dependentIndependent_probability_all μ (fun i a => i ∈ S → E i a)]
  have hi (i : ι) : (μ i).probability (fun x => i ∈ S → E i x) =
      if i ∈ S then (μ i).probability (E i) else 1 := by
    by_cases h : i ∈ S
    · simp [h]
    · simp [probability, h]
  simp only [hi]
  simp

lemma dependentIndependent_avoid {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) :
    (dependentIndependent μ).probability (avoidsEvents univ (fun i x => E i (x i))) =
      ∏ i, (1 - (μ i).probability (E i)) := by
  have he : avoidsEvents univ (fun i (x : ∀ i, A i) => E i (x i)) =
      (fun (x : ∀ i, A i) => ∀ i, ¬E i (x i)) := by funext x; simp [avoidsEvents]
  rw [he, dependentIndependent_probability_all μ (fun i a => ¬E i a)]
  simp only [probability_complement]

end FiniteLaw

noncomputable def elementarySymmetric {ι : Type*} (P : Finset ι) (a : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard j, ∏ i ∈ S, a i

lemma independent_intersectionMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) (P : Finset ι) (j : ℕ) :
    eventIntersectionMass (FiniteLaw.dependentIndependent μ) P
      (fun i x => E i (x i)) j = elementarySymmetric P
        (fun i => (μ i).probability (E i)) j := by
  simp only [eventIntersectionMass, elementarySymmetric,
    FiniteLaw.dependentIndependent_intersection]

/-- Exponential weighting bounds one elementary symmetric layer. This
avoids factorial estimates and gives the same finite-sieve tail. -/
theorem elementarySymmetric_exp_bound {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ P, 0 ≤ a i) (j : ℕ) (t : ℝ) (ht : 0 < t) :
    elementarySymmetric P a j ≤ Real.exp (t * ∑ i ∈ P, a i) / t ^ j := by
  have hm : t ^ j * elementarySymmetric P a j =
      ∑ S ∈ P.powersetCard j, ∏ i ∈ S, t * a i := by
    unfold elementarySymmetric
    rw [mul_sum]
    apply sum_congr rfl
    intro S hS
    rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp hS).2]
  have hsub : P.powersetCard j ⊆ P.powerset := by
    intro S hS
    exact mem_powerset.mpr (mem_powersetCard.mp hS).1
  have hb : t ^ j * elementarySymmetric P a j ≤ Real.exp (t * ∑ i ∈ P, a i) := by
    rw [hm]
    calc
      _ ≤ ∑ S ∈ P.powerset, ∏ i ∈ S, t * a i := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro S hS _
        exact prod_nonneg (fun i hi => mul_nonneg ht.le
          (ha i ((mem_powerset.mp hS) hi)))
      _ = ∏ i ∈ P, (1 + t * a i) := (prod_one_add P).symm
      _ ≤ ∏ i ∈ P, Real.exp (t * a i) := by
        apply prod_le_prod₀
        · intro i hi
          exact add_nonneg zero_le_one (mul_nonneg ht.le (ha i hi))
        · intro i _
          linarith [Real.add_one_le_exp (t * a i)]
      _ = Real.exp (∑ i ∈ P, t * a i) := (Real.exp_sum P _).symm
      _ = _ := by rw [mul_sum]
  exact (le_div_iff₀ (pow_pos ht j)).mpr (by simpa [mul_comm] using hb)

/-- A direct useful specialization: tail order `j` and total local mass
`M` give `exp(2M) / 2^j`. -/
lemma elementarySymmetric_two_bound {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ P, 0 ≤ a i) (j : ℕ) :
    elementarySymmetric P a j ≤ Real.exp (2 * ∑ i ∈ P, a i) / (2 : ℝ) ^ j :=
  elementarySymmetric_exp_bound P a ha j 2 (by norm_num)

/-- The next-layer tail is already at most `L⁻¹⁰⁰` once its order exceeds
`220 log L` and the total local mass is at most `5 log L`. The manuscript
uses the considerably larger order `1000 log L`. -/
theorem elementarySymmetric_log_tail {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ P, 0 ≤ a i) (j : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hmass : (∑ i ∈ P, a i) ≤ 5 * Real.log L)
    (hj : 220 * Real.log L ≤ (j : ℝ)) :
    elementarySymmetric P a j ≤ L ^ (-100 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hh
    linarith
  apply (elementarySymmetric_two_bound P a ha j).trans
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num),
    ← Real.exp_sub, Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have horder : 110 * Real.log L ≤ (j : ℝ) * Real.log 2 := by
    calc
      _ = (220 * Real.log L) * (1 / 2 : ℝ) := by ring
      _ ≤ (j : ℝ) * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hj (by norm_num)
      _ ≤ (j : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg j)
  nlinarith

/-- Finite sieve upper bound with the independent local model fully
evaluated. The only arithmetic premise is the error of each actual
intersection count. -/
theorem finite_independent_sieve_bound {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    {A : ι → Type*} [∀ i, Fintype (A i)]
    (actual : FiniteLaw α) (E : ι → α → Prop)
    (laws : ∀ i, FiniteLaw (A i)) (bad : ∀ i, A i → Prop)
    (r : ℕ) (err : Finset ι → ℝ)
    (herr : ∀ S ∈ (univ : Finset ι).powerset, S.card ≤ 2 * r →
      |actual.probability (eventIntersection E S) -
        ∏ i ∈ S, (laws i).probability (bad i)| ≤ err S) :
    actual.probability (avoidsEvents univ E) ≤
      (∏ i, (1 - (laws i).probability (bad i))) +
      elementarySymmetric univ (fun i => (laws i).probability (bad i)) (2 * r + 1) +
      sieveIntersectionError univ err (2 * r) := by
  have hh := bonferroni_transfer actual (FiniteLaw.dependentIndependent laws) univ
    E (fun i x => bad i (x i)) r err (fun S hS hcard => by
      rw [FiniteLaw.dependentIndependent_intersection]
      exact herr S hS hcard)
  simpa only [FiniteLaw.dependentIndependent_avoid, independent_intersectionMass] using hh

end TwoPointCorrelations

end OAI
