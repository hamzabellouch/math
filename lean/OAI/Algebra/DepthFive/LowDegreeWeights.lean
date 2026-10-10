import OAI.Algebra.DepthFive.DegreeWeight
import OAI.Algebra.DepthFive.DegreeProductBounds
import OAI.Algebra.DepthFive.SmallDegreeCorrections

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

lemma degreeWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (lam : ℝ) (e : ℕ) :
    0 ≤ degreeWeight q lam e :=
  Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg hq _)

lemma degreeWeight_le_five_mul_distance {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (lam : ℝ) (e : ℕ) :
    degreeWeight q lam e ≤ 5 * q ^ nearestIntegerDistance (lam * e) := by
  have hq1 : q ≤ 1 := by linarith
  have hd := nearestIntegerDistance_le_half (lam * e)
  have htail := Real.rpow_le_one hq.le hq1
    (show 0 ≤ 1 - 2 * nearestIntegerDistance (lam * e) by linarith)
  calc
    degreeWeight q lam e ≤ q ^ nearestIntegerDistance (lam * e) *
        (1 + 4 * q ^ (1 - 2 * nearestIntegerDistance (lam * e))) :=
      degreeWeight_le_nearest hq hqhalf lam e
    _ ≤ q ^ nearestIntegerDistance (lam * e) * 5 :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hq.le _)
    _ = _ := mul_comm _ _

lemma low_odd_degreeWeight_le {n s q : ℝ} (hn : 0 < n) (hs : 0 < s)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    {e : ℕ} (he : 0 < e) (helow : (e : ℝ) < n / (4 * s)) (hodd : Odd e) :
    degreeWeight q (1 / 2 - s / (2 * n)) e ≤ q ^ (degreeDistance n s e / 2) := by
  have hq1 : q ≤ 1 := by linarith
  have hd := degreeDistance_odd_ge hn hs he helow hodd
  have hp : q ^ (degreeDistance n s e / 2) ≤ q ^ ((3 : ℝ) / 16) :=
    Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith)
  have hp5 : 5 * q ^ (degreeDistance n s e / 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp (by norm_num)).trans hqsmall
  have hbound := degreeWeight_le_five_mul_distance hq hqhalf (1 / 2 - s / (2 * n)) e
  change degreeWeight q (1 / 2 - s / (2 * n)) e ≤ 5 * q ^ degreeDistance n s e at hbound
  calc
    degreeWeight q (1 / 2 - s / (2 * n)) e ≤ 5 * q ^ degreeDistance n s e := hbound
    _ = (5 * q ^ (degreeDistance n s e / 2)) * q ^ (degreeDistance n s e / 2) := by
      rw [mul_assoc, ← Real.rpow_add hq]
      congr 2
      ring
    _ ≤ 1 * q ^ (degreeDistance n s e / 2) :=
      mul_le_mul_of_nonneg_right hp5 (Real.rpow_nonneg hq.le _)
    _ = _ := one_mul _

lemma low_even_degreeWeight_le {n s q : ℝ} (hn : 0 < n) (hs : 0 < s)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    {e : ℕ} (he : 0 < e) (helow : (e : ℝ) < n / (4 * s)) (heven : Even e) :
    degreeWeight q (1 / 2 - s / (2 * n)) e ≤
      q ^ degreeDistance n s e * Real.exp (4 * q ^ (1 - s * e / n)) := by
  have hbound := degreeWeight_le_nearest hq hqhalf (1 / 2 - s / (2 * n)) e
  change degreeWeight q (1 / 2 - s / (2 * n)) e ≤ q ^ degreeDistance n s e *
    (1 + 4 * q ^ (1 - 2 * degreeDistance n s e)) at hbound
  have hexponent : 1 - 2 * degreeDistance n s e = 1 - s * e / n := by
    rw [degreeDistance_even hn hs he helow heven]
    ring
  rw [hexponent] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (by linarith [Real.add_one_le_exp (4 * q ^ (1 - s * e / n))])
    (Real.rpow_nonneg hq.le _))

lemma low_degreeWeight_le_with_correction {n s q : ℝ} (hn : 0 < n) (hs : 0 < s)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    {e : ℕ} (he : 0 < e) (helow : (e : ℝ) < n / (4 * s)) :
    degreeWeight q (1 / 2 - s / (2 * n)) e ≤
      q ^ (degreeDistance n s e / 2) * Real.exp (4 * q ^ (1 - s * e / n)) := by
  have hq1 : q ≤ 1 := by linarith
  rcases Nat.even_or_odd e with heven | hodd
  · refine (low_even_degreeWeight_le hn hs hq hqhalf he helow heven).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.rpow_le_rpow_of_exponent_ge hq hq1
    have hd : 0 ≤ degreeDistance n s e := nearestIntegerDistance_nonneg _
    linarith
  · refine (low_odd_degreeWeight_le hn hs hq hqhalf hqsmall he helow hodd).trans ?_
    have hexp : 1 ≤ Real.exp (4 * q ^ (1 - s * e / n)) :=
      Real.one_le_exp_iff.mpr (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
      (Real.rpow_nonneg hq.le (degreeDistance n s e / 2))

/-- The actual factor weights, rather than hypothetical costs, give the
all-low product saving in the circuit argument. -/
theorem low_degreeWeight_product_bound {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    {n s q : ℝ} (hn : 1 ≤ n) (hs : 0 < s)
    (hslo : Real.sqrt n / 2 ≤ s) (hshi : s ≤ Real.sqrt n)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hqsqrt : q ≤ 2 / Real.sqrt n)
    (hqpow : q ≤ n ^ (-(2 / 5 : ℝ))) (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    (he : ∀ i ∈ I, 0 < e i) (helow : ∀ i ∈ I, (e i : ℝ) < n / (4 * s))
    (hsum : ∑ i ∈ I, (e i : ℝ) = n) :
    (∏ i ∈ I, degreeWeight q (1 / 2 - s / (2 * n)) (e i)) ≤
      Real.exp (24 * Real.sqrt n) * n ^ (-Real.sqrt n / 20) := by
  have hn0 : 0 < n := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hcorr : (∑ i ∈ I, q ^ (1 - s * e i / n)) ≤ 6 * Real.sqrt n := by
    apply sum_small_degree_corrections_le I n s q (fun i => (e i : ℝ))
      hn0 hs.le hshi hq hq1 hqsqrt
    · intro i hi
      exact_mod_cast he i hi
    · intro i hi
      obtain ⟨_, h⟩ := low_degree_offset hn0 hs (he i hi) (helow i hi)
      have hid : s * e i / n = 2 * (s * e i / (2 * n)) := by ring
      rw [hid]
      linarith
    · exact hsum.le
  apply all_low_degree_product_bound I e
    (fun i => degreeWeight q (1 / 2 - s / (2 * n)) (e i))
    (fun i => 4 * q ^ (1 - s * e i / n)) hn hs hslo hq hq1 hqpow he helow hsum
  · exact fun i _ => degreeWeight_nonneg hq.le _ _
  · exact fun i hi => low_degreeWeight_le_with_correction hn0 hs hq hqhalf hqsmall
      (he i hi) (helow i hi)
  · rw [← Finset.mul_sum]
    linarith

end Problem335

end

end OAI
