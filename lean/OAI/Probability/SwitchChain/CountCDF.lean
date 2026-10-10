import OAI.Probability.SwitchChain.CountCoupling

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CountCoupling

def pairNormalizer (α β s : ℕ) : ℝ :=
  ∑ y ∈ Finset.range (s + 1), pairWeight α β s y

theorem pairNormalizer_pos (α β s : ℕ) : 0 < pairNormalizer α β s := by
  apply Finset.sum_pos
  · intro y hy
    exact pairWeight_pos α β s y
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

def pairProbability (α β s y : ℕ) : ℝ :=
  pairWeight α β s y / pairNormalizer α β s

theorem pairProbability_pos (α β s y : ℕ) : 0 < pairProbability α β s y :=
  div_pos (pairWeight_pos α β s y) (pairNormalizer_pos α β s)

theorem sum_pairProbability (α β s : ℕ) :
    (∑ y ∈ Finset.range (s + 1), pairProbability α β s y) = 1 := by
  unfold pairProbability
  rw [← Finset.sum_div]
  change pairNormalizer α β s / pairNormalizer α β s = 1
  exact div_self (ne_of_gt (pairNormalizer_pos α β s))

def pairPrefix (α β s k : ℕ) : ℝ :=
  ∑ y ∈ Finset.range k, pairProbability α β s y

theorem pairPrefix_eq_expectation (α β s k : ℕ) (hk : k ≤ s + 1) :
    pairPrefix α β s k =
      pairExpectation α β s (fun y => if y < k then 1 else 0) := by
  have hs : (Finset.range (s + 1)).filter (fun y => y < k) = Finset.range k := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  unfold pairPrefix pairProbability pairExpectation pairNormalizer
  rw [← Finset.sum_div]
  congr 1
  rw [← hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : y < k <;> simp [h]

theorem antitone_lower_indicator (k : ℕ) :
    Antitone (fun y : ℕ => if y < k then (1 : ℝ) else 0) := by
  intro y z hyz
  dsimp
  split_ifs <;> norm_num ; omega

theorem pairPrefix_succ_le (α β s k : ℕ) (hk : k ≤ s + 1) :
    pairPrefix α β (s + 1) k ≤ pairPrefix α β s k := by
  rw [pairPrefix_eq_expectation α β (s + 1) k (by omega),
    pairPrefix_eq_expectation α β s k hk]
  exact pairExpectation_succ_le_of_antitone α β s _ (antitone_lower_indicator k)

theorem pairExpectation_shift_le_succ_of_antitone (α β s : ℕ) (b : ℕ → ℝ)
    (hb : Antitone b) :
    pairExpectation α β s (fun y => b (y + 1)) ≤ pairExpectation α β (s + 1) b := by
  have h := pairExpectation_succ_le_shift α β s (fun y => -b y)
    (fun _ _ hij => neg_le_neg (hb hij))
  rw [pairExpectation_neg, pairExpectation_neg] at h
  linarith

theorem pairPrefix_le_succ_shift (α β s k : ℕ) (hk : k ≤ s + 1) :
    pairPrefix α β s k ≤ pairPrefix α β (s + 1) (k + 1) := by
  rw [pairPrefix_eq_expectation α β s k hk,
    pairPrefix_eq_expectation α β (s + 1) (k + 1) (by omega)]
  have h := pairExpectation_shift_le_succ_of_antitone α β s
    (fun y => if y < k + 1 then (1 : ℝ) else 0) (antitone_lower_indicator (k + 1))
  simpa only [Nat.add_lt_add_iff_right] using h

def pairBirthMass (α β s y : ℕ) : ℝ :=
  pairPrefix α β s (y + 1) - pairPrefix α β (s + 1) (y + 1)

theorem pairBirthMass_nonneg (α β s y : ℕ) (hy : y ≤ s) :
    0 ≤ pairBirthMass α β s y := by
  exact sub_nonneg.mpr (pairPrefix_succ_le α β s (y + 1) (by omega))

theorem pairBirthMass_le_probability (α β s y : ℕ) (hy : y ≤ s) :
    pairBirthMass α β s y ≤ pairProbability α β s y := by
  have h := pairPrefix_le_succ_shift α β s y (by omega)
  unfold pairBirthMass pairPrefix at *
  rw [Finset.sum_range_succ]
  linarith

theorem pairExpectation_eq_sum_probability (α β s : ℕ) (b : ℕ → ℝ) :
    pairExpectation α β s b =
      ∑ y ∈ Finset.range (s + 1), pairProbability α β s y * b y := by
  unfold pairExpectation pairProbability pairNormalizer
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  ring

@[simp] theorem pairPrefix_zero (α β s : ℕ) : pairPrefix α β s 0 = 0 := by
  simp [pairPrefix]

theorem pairPrefix_succ (α β s y : ℕ) :
    pairPrefix α β s (y + 1) = pairPrefix α β s y + pairProbability α β s y := by
  exact Finset.sum_range_succ _ _

theorem pairPrefix_total (α β s : ℕ) : pairPrefix α β s (s + 1) = 1 :=
  sum_pairProbability α β s

def countObservable (s : ℕ) (b c : ℕ → ℝ) (y : ℕ) : ℝ := b y + c (s - y)

theorem countObservable_stay_difference (s y : ℕ) (hy : y ≤ s)
    (b c : ℕ → ℝ) :
    countObservable (s + 1) b c y - countObservable s b c y =
      c (s - y + 1) - c (s - y) := by
  unfold countObservable
  rw [show s + 1 - y = s - y + 1 by omega]
  ring

theorem countObservable_birth_difference (s y : ℕ) (hy : y ≤ s)
    (b c : ℕ → ℝ) :
    countObservable (s + 1) b c (y + 1) - countObservable s b c y =
      b (y + 1) - b y := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hy
  unfold countObservable
  rw [Nat.add_sub_add_right]
  ring

theorem countObservable_stay_bound (s y : ℕ) (hy : y ≤ s)
    (b c : ℕ → ℝ) (M : ℝ)
    (hc : ∀ t ≤ s, |c (t + 1) - c t| ≤ M) :
    |countObservable (s + 1) b c y - countObservable s b c y| ≤ M := by
  rw [countObservable_stay_difference s y hy]
  exact hc (s - y) (Nat.sub_le s y)

theorem countObservable_birth_bound (s y : ℕ) (hy : y ≤ s)
    (b c : ℕ → ℝ) (M : ℝ)
    (hb : ∀ t ≤ s, |b (t + 1) - b t| ≤ M) :
    |countObservable (s + 1) b c (y + 1) - countObservable s b c y| ≤ M := by
  rw [countObservable_birth_difference s y hy]
  exact hb y hy

end Problem315.CountCoupling

end

end OAI
