import Mathlib

namespace OAI

noncomputable section

namespace Problem335

/-- Distance to the nearest integer, with rounding used only to select a minimizer. -/
def nearestIntegerDistance (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma nearestIntegerDistance_nonneg (x : ℝ) : 0 ≤ nearestIntegerDistance x :=
  abs_nonneg _

lemma nearestIntegerDistance_le_half (x : ℝ) : nearestIntegerDistance x ≤ 1 / 2 :=
  abs_sub_round x

lemma nearestIntegerDistance_le (x : ℝ) (z : ℤ) :
    nearestIntegerDistance x ≤ |x - (z : ℝ)| :=
  round_le x z

lemma nearestIntegerDistance_even {e : ℕ} (he : Even e) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    nearestIntegerDistance ((e : ℝ) / 2 - δ) = δ := by
  rcases he with ⟨k, rfl⟩
  have hr : round (((k + k : ℕ) : ℝ) / 2 - δ) = (k : ℤ) := by
    apply round_eq_iff.mpr
    constructor <;> push_cast <;> linarith
  rw [nearestIntegerDistance, hr]
  push_cast
  rw [show ((k : ℝ) + k) / 2 - δ - k = -δ by ring]
  simpa using abs_of_nonpos (neg_nonpos.mpr hδ)

lemma nearestIntegerDistance_odd {e : ℕ} (he : Odd e) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    nearestIntegerDistance ((e : ℝ) / 2 - δ) = 1 / 2 - δ := by
  rcases he with ⟨k, rfl⟩
  have hr : round (((2 * k + 1 : ℕ) : ℝ) / 2 - δ) = (k : ℤ) := by
    apply round_eq_iff.mpr
    constructor <;> push_cast <;> linarith
  rw [nearestIntegerDistance, hr]
  push_cast
  rw [show ((2 * (k : ℝ) + 1) / 2 - δ - k) = 1 / 2 - δ by ring]
  exact abs_of_nonneg (sub_nonneg.mpr hδ')

lemma nearestIntegerDistance_half_sub_ge {e : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    δ ≤ nearestIntegerDistance ((e : ℝ) / 2 - δ) := by
  rcases Nat.even_or_odd e with he | he
  · rw [nearestIntegerDistance_even he hδ.le (by linarith)]
  · rw [nearestIntegerDistance_odd he hδ (by linarith)]
    linarith

/-- The degree-saving distance at slope `(n-s)/(2*n)`. -/
def degreeDistance (n s : ℝ) (e : ℕ) : ℝ :=
  nearestIntegerDistance ((1 / 2 - s / (2 * n)) * e)

lemma degreeDistance_eq_half_sub (n s : ℝ) (e : ℕ) :
    degreeDistance n s e = nearestIntegerDistance ((e : ℝ) / 2 - s * e / (2 * n)) := by
  unfold degreeDistance
  congr 1
  ring

lemma low_degree_offset {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    {e : ℕ} (he : 0 < e) (he' : (e : ℝ) < n / (4 * s)) :
    0 < s * e / (2 * n) ∧ s * e / (2 * n) < 1 / 8 := by
  constructor
  · positivity
  · have hmul : (e : ℝ) * (4 * s) < n :=
      (lt_div_iff₀ (by positivity : 0 < 4 * s)).mp he'
    apply (div_lt_iff₀ (by positivity : 0 < 2 * n)).mpr
    nlinarith

lemma degreeDistance_even {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    {e : ℕ} (he : 0 < e) (he' : (e : ℝ) < n / (4 * s)) (heven : Even e) :
    degreeDistance n s e = s * e / (2 * n) := by
  rw [degreeDistance_eq_half_sub]
  obtain ⟨hδ, hδ'⟩ := low_degree_offset hn hs he he'
  exact nearestIntegerDistance_even heven hδ.le (by linarith)

lemma degreeDistance_odd {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    {e : ℕ} (he : 0 < e) (he' : (e : ℝ) < n / (4 * s)) (hodd : Odd e) :
    degreeDistance n s e = 1 / 2 - s * e / (2 * n) := by
  rw [degreeDistance_eq_half_sub]
  obtain ⟨hδ, hδ'⟩ := low_degree_offset hn hs he he'
  exact nearestIntegerDistance_odd hodd hδ (by linarith)

lemma degreeDistance_ge {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    {e : ℕ} (he : 0 < e) (he' : (e : ℝ) < n / (4 * s)) :
    s * e / (2 * n) ≤ degreeDistance n s e := by
  rw [degreeDistance_eq_half_sub]
  obtain ⟨hδ, hδ'⟩ := low_degree_offset hn hs he he'
  exact nearestIntegerDistance_half_sub_ge hδ (by linarith)

lemma degreeDistance_odd_ge {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    {e : ℕ} (he : 0 < e) (he' : (e : ℝ) < n / (4 * s)) (hodd : Odd e) :
    3 / 8 ≤ degreeDistance n s e := by
  rw [degreeDistance_odd hn hs he he' hodd]
  obtain ⟨_, hδ'⟩ := low_degree_offset hn hs he he'
  linarith

open scoped BigOperators

lemma sum_degreeDistance_ge {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    (he : ∀ i ∈ I, 0 < e i) (he' : ∀ i ∈ I, (e i : ℝ) < n / (4 * s)) :
    s / (2 * n) * (∑ i ∈ I, (e i : ℝ)) ≤ ∑ i ∈ I, degreeDistance n s (e i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    s / (2 * n) * (e i : ℝ) = s * e i / (2 * n) := by ring
    _ ≤ degreeDistance n s (e i) := degreeDistance_ge hn hs (he i hi) (he' i hi)

lemma sum_degreeDistance_ge_half {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    (he : ∀ i ∈ I, 0 < e i) (he' : ∀ i ∈ I, (e i : ℝ) < n / (4 * s))
    (hsum : ∑ i ∈ I, (e i : ℝ) = n) :
    s / 2 ≤ ∑ i ∈ I, degreeDistance n s (e i) := by
  have h := sum_degreeDistance_ge I e hn hs he he'
  rw [hsum] at h
  convert h using 1
  field_simp

lemma prod_degreeDistance_rpow_le {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    {n s q : ℝ} (hn : 0 < n) (hs : 0 < s) (hq : 0 < q) (hq' : q ≤ 1)
    (he : ∀ i ∈ I, 0 < e i) (he' : ∀ i ∈ I, (e i : ℝ) < n / (4 * s))
    (hsum : ∑ i ∈ I, (e i : ℝ) = n) :
    (∏ i ∈ I, q ^ (degreeDistance n s (e i) / 2)) ≤ q ^ (s / 4) := by
  rw [← Real.rpow_sum_of_pos hq]
  apply Real.rpow_le_rpow_of_exponent_ge hq hq'
  rw [← Finset.sum_div]
  have h := sum_degreeDistance_ge_half I e hn hs he he' hsum
  linarith

end Problem335

end

end OAI
