import Mathlib

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337.CubeFreeDensity

/-- Positive integers up to `N` divisible by a nontrivial integer cube. -/
def bad (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n => ∃ k : ℕ, 2 ≤ k ∧ k ^ 3 ∣ n)

/-- Positive cube-free integers up to `N`. -/
def good (N : ℕ) : Finset ℕ := Finset.Icc 1 N \ bad N

@[simp] theorem mem_bad {N n : ℕ} :
    n ∈ bad N ↔ 1 ≤ n ∧ n ≤ N ∧ ∃ k : ℕ, 2 ≤ k ∧ k ^ 3 ∣ n := by
  classical
  simp only [bad, Finset.mem_filter, Finset.mem_Icc, and_assoc]

@[simp] theorem mem_good {N n : ℕ} :
    n ∈ good N ↔ 1 ≤ n ∧ n ≤ N ∧ ∀ k : ℕ, 2 ≤ k → ¬ k ^ 3 ∣ n := by
  classical
  simp only [good, Finset.mem_sdiff, Finset.mem_Icc, mem_bad]
  constructor
  · rintro ⟨⟨hn1, hnN⟩, hbad⟩
    exact ⟨hn1, hnN, fun k hk hdiv => hbad ⟨hn1, hnN, k, hk, hdiv⟩⟩
  · rintro ⟨hn1, hnN, hfree⟩
    exact ⟨⟨hn1, hnN⟩, fun ⟨_, _, k, hk, hdiv⟩ => hfree k hk hdiv⟩

/-- A telescoping majorant with no infinite-series or asymptotic input. -/
theorem reciprocal_cube_le (j : ℕ) :
    1 / ((j : ℝ) + 2) ^ 3 ≤
      (1 / 4 : ℝ) * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) := by
  have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have hden : 4 * ((j : ℝ) + 1) * ((j : ℝ) + 2) ≤ ((j : ℝ) + 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (j : ℝ)) h2.le]
  calc
    _ ≤ 1 / (4 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by field_simp; ring

/-- The reciprocal cubes starting at two have every finite sum at most one
quarter. The intentionally elementary constant leaves room above density 2/3. -/
theorem sum_reciprocal_cubes_le (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 2) ^ 3) ≤ (1 / 4 : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        (1 / 4 : ℝ) * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) :=
      Finset.sum_le_sum (fun j _ => reciprocal_cube_le j)
    _ = (1 / 4 : ℝ) * (1 - 1 / ((N : ℝ) + 1)) := by
      rw [← Finset.mul_sum]
      have h := Finset.sum_range_sub' (fun j : ℕ => 1 / ((j : ℝ) + 1)) N
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, div_one,
        add_assoc, one_add_one_eq_two] using congrArg (fun x : ℝ => (1 / 4) * x) h
    _ ≤ _ := by
      have h : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith

theorem card_positive_multiples (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hI, Nat.Ioc_filter_dvd_card_eq_div]

/-- An exact finite union bound, including all composite cube bases. -/
theorem card_bad_le_sum (N : ℕ) :
    (bad N).card ≤ ∑ j ∈ Finset.range N, N / (j + 2) ^ 3 := by
  classical
  let A : ℕ → Finset ℕ := fun j =>
    (Finset.Icc 1 N).filter (fun n => (j + 2) ^ 3 ∣ n)
  have hsub : bad N ⊆ (Finset.range N).biUnion A := by
    intro n hn
    obtain ⟨hn1, hnN, k, hk, hkdiv⟩ := mem_bad.mp hn
    have hkN : k ≤ N := (Nat.le_self_pow (by norm_num : 3 ≠ 0) k).trans
      ((Nat.le_of_dvd hn1 hkdiv).trans hnN)
    refine Finset.mem_biUnion.mpr ⟨k - 2, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp [A]
    rw [Nat.sub_add_cancel hk]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, hkdiv⟩
  calc
    _ ≤ ((Finset.range N).biUnion A).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range N, (A j).card := Finset.card_biUnion_le
    _ = _ := by simp only [A, card_positive_multiples]

/-- At most one quarter of any initial interval is divisible by a nontrivial
cube. This is uniform in the endpoint and has no additive error term. -/
theorem card_bad_le_quarter (N : ℕ) :
    ((bad N).card : ℝ) ≤ (N : ℝ) / 4 := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, ((N / (j + 2) ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast card_bad_le_sum N
    _ ≤ ∑ j ∈ Finset.range N, (N : ℝ) / ((j : ℝ) + 2) ^ 3 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using
        (Nat.cast_div_le (m := N) (n := (j + 2) ^ 3) :
          ((N / (j + 2) ^ 3 : ℕ) : ℝ) ≤ (N : ℝ) / ((j + 2) ^ 3 : ℕ))
    _ = (N : ℝ) * ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 2) ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (N : ℝ) * (1 / 4) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_cubes_le N) (Nat.cast_nonneg N)
    _ = _ := by ring

/-- Consequently cube-free moduli have the explicit uniform density 3/4. -/
theorem card_good_ge_three_quarters (N : ℕ) :
    (3 : ℝ) * N / 4 ≤ (good N).card := by
  have hsub : bad N ⊆ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(mem_bad.mp hn).1, (mem_bad.mp hn).2.1⟩
  have hcard : (good N).card + (bad N).card = N := by
    simpa only [good, Nat.card_Icc, Nat.add_sub_cancel] using
      Finset.card_sdiff_add_card_eq_card hsub
  have hcardR : ((good N).card : ℝ) + (bad N).card = N := by exact_mod_cast hcard
  linarith [card_bad_le_quarter N]

/-- Deleting fewer than `N/12` further exceptional moduli still leaves the
strict density `2/3` required by the dense rational-supply completion. -/
theorem card_good_sdiff_gt_two_thirds (N : ℕ) (E : Finset ℕ)
    (hE : (E.card : ℝ) < (N : ℝ) / 12) :
    (2 : ℝ) * N / 3 < (good N \ E).card := by
  have hcard : ((good N).card : ℝ) ≤ (good N \ E).card + E.card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card :
      (good N).card ≤ (good N \ E).card + E.card)
  linarith [card_good_ge_three_quarters N]

theorem prime_cube_not_dvd_of_mem_good {N n p : ℕ} (hn : n ∈ good N)
    (hp : p.Prime) : ¬ p ^ 3 ∣ n :=
  (mem_good.mp hn).2.2 p hp.two_le

end Problem337.CubeFreeDensity

end

end OAI
