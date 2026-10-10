import OAI.Algebra.DepthFive.DegreeDiscrepancy
import OAI.Algebra.DepthFive.DegreeDistances

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The geometric majorant for weights at the integers around a chosen center. -/
def latticeMajorant (q d : ℝ) (z : ℤ) : ℝ :=
  if z = 0 then q ^ d else q ^ (1 - d) * q ^ (z.natAbs - 1)

lemma latticeMajorant_nonneg {q : ℝ} (hq : 0 ≤ q) (d : ℝ) (z : ℤ) :
    0 ≤ latticeMajorant q d z := by
  unfold latticeMajorant
  split_ifs
  · exact Real.rpow_nonneg hq _
  · exact mul_nonneg (Real.rpow_nonneg hq _) (pow_nonneg hq _)

lemma hasSum_latticeMajorant {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (d : ℝ) :
    HasSum (latticeMajorant q d)
      (q ^ d + 2 * (q ^ (1 - d) / (1 - q))) := by
  have hgeom : HasSum (fun n : ℕ => q ^ (1 - d) * q ^ n)
      (q ^ (1 - d) / (1 - q)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hq hq1).mul_left (q ^ (1 - d))
  have hpval (n : ℕ) : latticeMajorant q d ((n : ℤ) + 1) =
      q ^ (1 - d) * q ^ n := by
    have hne : (n : ℤ) + 1 ≠ 0 := by omega
    have habs : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    simp only [latticeMajorant, ite_eq_right hne, habs, Nat.add_sub_cancel]
  have hnval (n : ℕ) : latticeMajorant q d (-((n : ℤ) + 1)) =
      q ^ (1 - d) * q ^ n := by
    have hne : -((n : ℤ) + 1) ≠ 0 := by omega
    have habs : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    simp only [latticeMajorant, ite_eq_right hne, Int.natAbs_neg, habs, Nat.add_sub_cancel]
  have hp : HasSum (fun n : ℕ => latticeMajorant q d ((n : ℤ) + 1))
      (q ^ (1 - d) / (1 - q)) := by
    simpa only [hpval] using hgeom
  have hn : HasSum (fun n : ℕ => latticeMajorant q d (-((n : ℤ) + 1)))
      (q ^ (1 - d) / (1 - q)) := by
    simpa only [hnval] using hgeom
  have h := hp.of_add_one_of_neg_add_one hn
  have hzero : latticeMajorant q d 0 = q ^ d := by simp [latticeMajorant]
  rw [hzero] at h
  convert h using 1
  ring

lemma rpow_abs_sub_le_latticeMajorant {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (y : ℝ) (z : ℤ) :
    q ^ |(z : ℝ) - y| ≤ latticeMajorant q |y| z := by
  by_cases hz : z = 0
  · subst z
    simp [latticeMajorant]
  have hzpos : 1 ≤ z.natAbs := by
    have := Int.natAbs_pos.mpr hz
    omega
  have htriangle : (z.natAbs : ℝ) - |y| ≤ |(z : ℝ) - y| := by
    have h := abs_sub_abs_le_abs_sub (z : ℝ) y
    have heq : |(z : ℝ)| = (z.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]
      simp
    rw [heq] at h
    exact h
  calc
    q ^ |(z : ℝ) - y| ≤ q ^ ((z.natAbs : ℝ) - |y|) :=
      Real.rpow_le_rpow_of_exponent_ge hq hq1 htriangle
    _ = latticeMajorant q |y| z := by
      rw [latticeMajorant, ite_eq_right hz]
      have he : (z.natAbs : ℝ) - |y| = (1 - |y|) + ((z.natAbs - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hzpos]
        norm_num
      rw [he, Real.rpow_add hq, Real.rpow_natCast]

lemma sum_lattice_rpow_le {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (y : ℝ) (s : Finset ℤ) :
    ∑ z ∈ s, q ^ |(z : ℝ) - y| ≤
      q ^ |y| + 2 * (q ^ (1 - |y|) / (1 - q)) := by
  have hs := hasSum_latticeMajorant hq.le hq1 |y|
  calc
    ∑ z ∈ s, q ^ |(z : ℝ) - y| ≤ ∑ z ∈ s, latticeMajorant q |y| z :=
      Finset.sum_le_sum (fun z _ => rpow_abs_sub_le_latticeMajorant hq hq1.le y z)
    _ ≤ ∑' z : ℤ, latticeMajorant q |y| z :=
      hs.summable.sum_le_tsum s (fun z _ => latticeMajorant_nonneg hq.le |y| z)
    _ = _ := hs.tsum_eq

lemma sum_nat_rpow_le {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (x : ℝ) (s : Finset ℕ) :
    ∑ i ∈ s, q ^ |(i : ℝ) - x| ≤
      q ^ nearestIntegerDistance x +
        2 * (q ^ (1 - nearestIntegerDistance x) / (1 - q)) := by
  unfold nearestIntegerDistance
  have h := sum_lattice_rpow_le hq hq1 (x - (round x : ℝ))
    (s.image (fun i : ℕ => (i : ℤ) - round x))
  rw [Finset.sum_image] at h
  · convert h using 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Int.cast_sub, Int.cast_natCast]
    congr 2
    ring
  · intro a ha b hb hab
    exact_mod_cast sub_left_injective hab

lemma rpow_geometric_bound {q d : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2) :
    q ^ d + 2 * (q ^ (1 - d) / (1 - q)) ≤
      q ^ d * (1 + 4 * q ^ (1 - 2 * d)) := by
  have hden : 0 < 1 - q := by linarith
  have hnum : 0 ≤ q ^ (1 - d) := Real.rpow_nonneg hq.le _
  have hdiv : q ^ (1 - d) / (1 - q) ≤ 2 * q ^ (1 - d) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hmul : q ^ d * q ^ (1 - 2 * d) = q ^ (1 - d) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  nlinarith

lemma rpow_geometric_bound_le_five {q d : ℝ} (hq : 0 < q)
    (hqhalf : q ≤ 1 / 2) (hd : 0 ≤ d) (hdhalf : d ≤ 1 / 2) :
    q ^ d * (1 + 4 * q ^ (1 - 2 * d)) ≤ 5 := by
  have hq1 : q ≤ 1 := by linarith
  have ha := Real.rpow_le_one hq.le hq1 hd
  have hb := Real.rpow_le_one hq.le hq1 (show 0 ≤ 1 - 2 * d by linarith)
  have hapos := Real.rpow_nonneg hq.le d
  have hbpos := Real.rpow_nonneg hq.le (1 - 2 * d)
  nlinarith

lemma sum_nat_rpow_le_nearest {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (x : ℝ) (s : Finset ℕ) :
    ∑ i ∈ s, q ^ |(i : ℝ) - x| ≤
      q ^ nearestIntegerDistance x * (1 + 4 * q ^ (1 - 2 * nearestIntegerDistance x)) :=
  (sum_nat_rpow_le hq (by linarith) x s).trans (rpow_geometric_bound hq hqhalf)

lemma sum_nat_rpow_le_five {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (x : ℝ) (s : Finset ℕ) :
    ∑ i ∈ s, q ^ |(i : ℝ) - x| ≤ 5 :=
  (sum_nat_rpow_le_nearest hq hqhalf x s).trans
    (rpow_geometric_bound_le_five hq hqhalf
      (nearestIntegerDistance_nonneg x) (nearestIntegerDistance_le_half x))

/-- The nearest-integer geometric estimate for the manuscript's factor weight. -/
theorem degreeWeight_le_nearest {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (lam : ℝ) (e : ℕ) :
    degreeWeight q lam e ≤
      q ^ nearestIntegerDistance (lam * e) *
        (1 + 4 * q ^ (1 - 2 * nearestIntegerDistance (lam * e))) :=
  sum_nat_rpow_le_nearest hq hqhalf (lam * e) (Finset.range (e + 1))

/-- The sharper uniform estimate retaining the nearest-integer saving. -/
theorem degreeWeight_le_five_mul {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (lam : ℝ) (e : ℕ) :
    degreeWeight q lam e ≤ 5 * q ^ nearestIntegerDistance (lam * e) := by
  have h := degreeWeight_le_nearest hq hqhalf lam e
  have hb := Real.rpow_le_one hq.le (show q ≤ 1 by linarith)
    (show 0 ≤ 1 - 2 * nearestIntegerDistance (lam * e) by
      linarith [nearestIntegerDistance_le_half (lam * e)])
  have ha := Real.rpow_nonneg hq.le (nearestIntegerDistance (lam * e))
  nlinarith

/-- Uniform upper bound for each factor weight, including arbitrarily high degrees. -/
theorem degreeWeight_le_five {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (lam : ℝ) (e : ℕ) : degreeWeight q lam e ≤ 5 :=
  sum_nat_rpow_le_five hq hqhalf (lam * e) (Finset.range (e + 1))

end Problem335

end

end OAI
