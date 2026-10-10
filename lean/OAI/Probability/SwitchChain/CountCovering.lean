import OAI.Probability.SwitchChain.CountCoupling

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CountCoupling

def prefixMass (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, p i

theorem adjacent_transport_identity (p q f : ℕ → ℝ) (s : ℕ)
    (hpEnd : p (s + 1) = 0)
    (hmass : prefixMass p (s + 1) = prefixMass q (s + 2)) :
    (∑ i ∈ Finset.range (s + 2), q i * f i) -
        (∑ i ∈ Finset.range (s + 1), p i * f i) =
      ∑ i ∈ Finset.range (s + 1),
        (prefixMass p (i + 1) - prefixMass q (i + 1)) * (f (i + 1) - f i) := by
  have htotal : (∑ i ∈ Finset.range (s + 2), (q i - p i)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_succ (f := p)]
    change prefixMass q (s + 2) - (prefixMass p (s + 1) + p (s + 1)) = 0
    rw [hpEnd, add_zero, hmass, sub_self]
  have hab := Finset.sum_range_by_parts f (fun i => q i - p i) (s + 2)
  simp only [smul_eq_mul, htotal, mul_zero, zero_sub,
    show s + 2 - 1 = s + 1 by omega] at hab
  calc
    _ = ∑ i ∈ Finset.range (s + 2), f i * (q i - p i) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [Finset.sum_range_succ (f := fun i => f i * p i)]
      simp only [hpEnd, mul_zero, add_zero]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
    _ = -(∑ i ∈ Finset.range (s + 1),
        (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), (q j - p j)) := hab
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [prefixMass, Finset.sum_sub_distrib]
      ring

theorem adjacent_two_coordinate_expectation_bound
    (p q b c : ℕ → ℝ) (s : ℕ) (M : ℝ)
    (hpEnd : p (s + 1) = 0)
    (hpMass : prefixMass p (s + 1) = 1)
    (hqMass : prefixMass q (s + 2) = 1)
    (hinterlace : ∀ i ≤ s,
      0 ≤ prefixMass p (i + 1) - prefixMass q (i + 1) ∧
      prefixMass p (i + 1) - prefixMass q (i + 1) ≤ p i)
    (hb : ∀ i ≤ s, |b (i + 1) - b i| ≤ M)
    (hc : ∀ i ≤ s, |c (i + 1) - c i| ≤ M) :
    |(∑ i ∈ Finset.range (s + 2), q i * (b i + c (s + 1 - i))) -
      (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s - i)))| ≤ M := by
  let δ : ℕ → ℝ := fun i => prefixMass p (i + 1) - prefixMass q (i + 1)
  have hid := adjacent_transport_identity p q (fun i => b i + c (s + 1 - i)) s
    hpEnd (hpMass.trans hqMass.symm)
  have hexpand :
      (∑ i ∈ Finset.range (s + 2), q i * (b i + c (s + 1 - i))) -
        (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s - i))) =
      ∑ i ∈ Finset.range (s + 1),
        ((p i - δ i) * (c (s - i + 1) - c (s - i)) +
          δ i * (b (i + 1) - b i)) := by
    calc
      _ = ((∑ i ∈ Finset.range (s + 2), q i * (b i + c (s + 1 - i))) -
          (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s + 1 - i)))) +
          ((∑ i ∈ Finset.range (s + 1), p i * (b i + c (s + 1 - i))) -
          (∑ i ∈ Finset.range (s + 1), p i * (b i + c (s - i)))) := by ring
      _ = _ := by
        rw [hid, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have his : i ≤ s := by have := Finset.mem_range.mp hi; omega
        have hsub : s + 1 - i = s - i + 1 := by omega
        have hsub' : s + 1 - (i + 1) = s - i := by omega
        simp only [hsub, hsub', δ]
        ring
  rw [hexpand]
  calc
    _ ≤ ∑ i ∈ Finset.range (s + 1),
        |(p i - δ i) * (c (s - i + 1) - c (s - i)) +
          δ i * (b (i + 1) - b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (s + 1), p i * M := by
      apply Finset.sum_le_sum
      intro i hi
      have his : i ≤ s := by have := Finset.mem_range.mp hi; omega
      have hd0 : 0 ≤ δ i := (hinterlace i his).1
      have hdp : δ i ≤ p i := (hinterlace i his).2
      calc
        _ ≤ |(p i - δ i) * (c (s - i + 1) - c (s - i))| +
            |δ i * (b (i + 1) - b i)| := abs_add_le _ _
        _ = (p i - δ i) * |c (s - i + 1) - c (s - i)| +
            δ i * |b (i + 1) - b i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hdp), abs_of_nonneg hd0]
        _ ≤ (p i - δ i) * M + δ i * M := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hc (s - i) (Nat.sub_le _ _)) (sub_nonneg.mpr hdp))
            (mul_le_mul_of_nonneg_left (hb i his) hd0)
        _ = p i * M := by ring
    _ = M := by rw [← Finset.sum_mul]; change prefixMass p (s + 1) * M = M; rw [hpMass, one_mul]

def coveredPairProbability (α β s y : ℕ) : ℝ :=
  if y ≤ s then pairWeight α β s y /
    (∑ z ∈ Finset.range (s + 1), pairWeight α β s z) else 0

theorem pairWeight_mass_pos (α β s : ℕ) :
    0 < ∑ y ∈ Finset.range (s + 1), pairWeight α β s y := by
  apply Finset.sum_pos
  · intro y hy
    exact pairWeight_pos α β s y
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

theorem coveredPairProbability_mass (α β s : ℕ) :
    prefixMass (coveredPairProbability α β s) (s + 1) = 1 := by
  unfold prefixMass
  calc
    _ = ∑ y ∈ Finset.range (s + 1), pairWeight α β s y /
        (∑ z ∈ Finset.range (s + 1), pairWeight α β s z) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hys : y ≤ s := by have := Finset.mem_range.mp hy; omega
      simp only [coveredPairProbability, ite_eq_left hys]
    _ = 1 := by
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt (pairWeight_mass_pos α β s))

theorem pairExpectation_eq_probability_sum (α β s : ℕ) (b : ℕ → ℝ) :
    pairExpectation α β s b =
      ∑ y ∈ Finset.range (s + 1), coveredPairProbability α β s y * b y := by
  unfold pairExpectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  have hys : y ≤ s := by have := Finset.mem_range.mp hy; omega
  simp only [coveredPairProbability, ite_eq_left hys]
  ring

theorem probability_prefix_eq_expectation (α β s k : ℕ) (hk : k ≤ s + 1) :
    prefixMass (coveredPairProbability α β s) k =
      pairExpectation α β s (fun y => if y < k then 1 else 0) := by
  rw [pairExpectation_eq_probability_sum]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hset : (Finset.range (s + 1)).filter (fun y => y < k) = Finset.range k := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset]
  rfl

theorem covered_pairExpectation_shift_le_succ_of_antitone (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Antitone b) :
    pairExpectation α β s (fun y => b (y + 1)) ≤ pairExpectation α β (s + 1) b := by
  have h := pairExpectation_succ_le_shift α β s (fun y => -b y)
    (fun _ _ hij => neg_le_neg (hb hij))
  rw [pairExpectation_neg, pairExpectation_neg] at h
  linarith

theorem coveredPairProbability_interlace (α β s i : ℕ) (hi : i ≤ s) :
    0 ≤ prefixMass (coveredPairProbability α β s) (i + 1) -
      prefixMass (coveredPairProbability α β (s + 1)) (i + 1) ∧
    prefixMass (coveredPairProbability α β s) (i + 1) -
      prefixMass (coveredPairProbability α β (s + 1)) (i + 1) ≤
        coveredPairProbability α β s i := by
  have hantitone (k : ℕ) : Antitone (fun y : ℕ => if y < k then (1 : ℝ) else 0) := by
    intro y z hyz
    dsimp only
    split_ifs <;> norm_num ; omega
  have hfirst := pairExpectation_succ_le_of_antitone α β s
    (fun y => if y < i + 1 then (1 : ℝ) else 0) (hantitone (i + 1))
  rw [← probability_prefix_eq_expectation α β (s + 1) (i + 1) (by omega),
    ← probability_prefix_eq_expectation α β s (i + 1) (by omega)] at hfirst
  refine ⟨sub_nonneg.mpr hfirst, ?_⟩
  have hsecond := covered_pairExpectation_shift_le_succ_of_antitone α β s
    (fun y => if y < i + 1 then (1 : ℝ) else 0) (hantitone (i + 1))
  simp only [Nat.add_lt_add_iff_right] at hsecond
  rw [← probability_prefix_eq_expectation α β s i (by omega),
    ← probability_prefix_eq_expectation α β (s + 1) (i + 1) (by omega)] at hsecond
  have hprefix : prefixMass (coveredPairProbability α β s) (i + 1) =
      prefixMass (coveredPairProbability α β s) i + coveredPairProbability α β s i := by
    exact Finset.sum_range_succ _ _
  linarith

theorem pairExpectation_adjacent_sum_bound (α β s : ℕ) (b c : ℕ → ℝ) (M : ℝ)
    (hb : ∀ i ≤ s, |b (i + 1) - b i| ≤ M)
    (hc : ∀ i ≤ s, |c (i + 1) - c i| ≤ M) :
    |pairExpectation α β (s + 1) (fun i => b i + c (s + 1 - i)) -
      pairExpectation α β s (fun i => b i + c (s - i))| ≤ M := by
  rw [pairExpectation_eq_probability_sum, pairExpectation_eq_probability_sum]
  exact adjacent_two_coordinate_expectation_bound
    (coveredPairProbability α β s) (coveredPairProbability α β (s + 1)) b c s M
    (by simp [coveredPairProbability]) (coveredPairProbability_mass α β s)
    (coveredPairProbability_mass α β (s + 1)) (coveredPairProbability_interlace α β s) hb hc

end Problem315.CountCoupling

end

end OAI
