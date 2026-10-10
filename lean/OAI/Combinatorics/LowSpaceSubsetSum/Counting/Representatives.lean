import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Deficiency
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Entropy
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Resources
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

namespace OAI

/-!
# Many distinct weights at one prescribed cardinality

The first representative-selection step in the low-deficiency survival proof.
Complementation allows the selected cardinality to be at most half the domain.
All cardinalities count distinct integer weights, not subset occurrences.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sumsAtSize (a : ι → ℤ) (V : Finset ι) (k : ℕ) : Finset ℤ :=
  (V.powersetCard k).image (weight a)

theorem mem_sumsAtSize (a : ι → ℤ) (V : Finset ι) (k : ℕ) (x : ℤ) :
    x ∈ sumsAtSize a V k ↔ ∃ S ⊆ V, S.card = k ∧ weight a S = x := by
  simp only [sumsAtSize, Finset.mem_image, Finset.mem_powersetCard]
  aesop

theorem weight_complement (a : ι → ℤ) {S V : Finset ι} (hS : S ⊆ V) :
    weight a (V \ S) = weight a V - weight a S := by
  have hd : Disjoint S (V \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiVS
    exact (Finset.mem_sdiff.mp hiVS).2 hiS
  have h := weight_union a hd
  rw [Finset.union_sdiff_of_subset hS] at h
  omega

theorem sumsAtSize_complement (a : ι → ℤ) (V : Finset ι) {k : ℕ}
    (hk : k ≤ V.card) :
    sumsAtSize a V (V.card - k) = (sumsAtSize a V k).image (fun x => weight a V - x) := by
  ext x
  constructor
  · intro hx
    obtain ⟨S, hS, hcS, rfl⟩ := (mem_sumsAtSize a V (V.card - k) x).mp hx
    refine Finset.mem_image.mpr ⟨weight a (V \ S), ?_, ?_⟩
    · apply (mem_sumsAtSize a V k _).mpr
      refine ⟨V \ S, Finset.sdiff_subset, ?_, rfl⟩
      rw [Finset.card_sdiff_of_subset hS, hcS]
      omega
    · rw [weight_complement a hS]
      omega
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨S, hS, hcS, rfl⟩ := (mem_sumsAtSize a V k y).mp hy
    apply (mem_sumsAtSize a V (V.card - k) _).mpr
    refine ⟨V \ S, Finset.sdiff_subset, ?_, weight_complement a hS⟩
    rw [Finset.card_sdiff_of_subset hS, hcS]

theorem sumsAtSize_complement_card (a : ι → ℤ) (V : Finset ι) {k : ℕ}
    (hk : k ≤ V.card) :
    (sumsAtSize a V (V.card - k)).card = (sumsAtSize a V k).card := by
  rw [sumsAtSize_complement a V hk]
  apply Finset.card_image_of_injective
  intro x y h
  exact sub_right_injective h

theorem distinctSumCount_le_sum_sizes (a : ι → ℤ) (V : Finset ι) :
    distinctSumCount a V ≤ ∑ k ∈ Finset.range (V.card + 1), (sumsAtSize a V k).card := by
  classical
  have hsub : distinctSums a V ⊆
      (Finset.range (V.card + 1)).biUnion (sumsAtSize a V) := by
    intro x hx
    obtain ⟨S, hS, rfl⟩ := (mem_distinctSums a V x).mp hx
    apply Finset.mem_biUnion.mpr
    refine ⟨S.card, Finset.mem_range.mpr (by have := Finset.card_le_card hS; omega), ?_⟩
    exact (mem_sumsAtSize a V S.card _).mpr ⟨S, hS, rfl, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- Pigeonhole selection of one size, followed by complementation if necessary. -/
theorem exists_many_distinct_weights_at_size (a : ι → ℤ) (V : Finset ι) :
    ∃ k ≤ V.card / 2,
      distinctSumCount a V ≤ (V.card + 1) * (sumsAtSize a V k).card := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range (V.card + 1))
    (fun k => (sumsAtSize a V k).card) (Finset.nonempty_range_iff.mpr (by omega))
  have hkV : k ≤ V.card := by have := Finset.mem_range.mp hk; omega
  have hN : distinctSumCount a V ≤ (V.card + 1) * (sumsAtSize a V k).card := by
    apply (distinctSumCount_le_sum_sizes a V).trans
    simpa using Finset.sum_le_card_nsmul (Finset.range (V.card + 1))
      (fun i => (sumsAtSize a V i).card) _ hmax
  by_cases hhalf : k ≤ V.card / 2
  · exact ⟨k, hhalf, hN⟩
  · refine ⟨V.card - k, by omega, ?_⟩
    rwa [sumsAtSize_complement_card a V hkV]

/-- The exact exponential form of the distinct-weight count. -/
theorem two_pow_card_sub_deficiency (a : ι → ℤ) (V : Finset ι) :
    (2 : ℝ) ^ ((V.card : ℝ) - deficiency a V) = distinctSumCount a V := by
  simp only [deficiency, sub_sub_cancel]
  exact Real.rpow_logb (by norm_num) (by norm_num) (distinctSumCount_pos_real a V)

/-- The representation proof's first distinct-weight lower bound. -/
theorem exists_representative_size (a : ι → ℤ) (V : Finset ι) :
    ∃ k ≤ V.card / 2,
      (2 : ℝ) ^ ((V.card : ℝ) - deficiency a V) / (V.card + 1) ≤
        (sumsAtSize a V k).card := by
  obtain ⟨k, hk, hN⟩ := exists_many_distinct_weights_at_size a V
  refine ⟨k, hk, ?_⟩
  rw [two_pow_card_sub_deficiency]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < V.card + 1)).mpr
  have hR : (distinctSumCount a V : ℝ) ≤ (V.card + 1) * (sumsAtSize a V k).card := by
    exact_mod_cast hN
  nlinarith

/-- Subsets of size at most one third cannot supply more than the corresponding
entropy bound, regardless of repeated values in the input. -/
theorem sumsAtSize_card_le_third_entropy (a : ι → ℤ) (V : Finset ι) {k : ℕ}
    (hV : 0 < V.card) (hk : 3 * k ≤ V.card) :
    ((sumsAtSize a V k).card : ℝ) ≤
      (2 : ℝ) ^ ((V.card : ℝ) * binaryEntropy (1 / 3)) := by
  have hn : (0 : ℝ) < V.card := by exact_mod_cast hV
  have hkV : k ≤ V.card := by omega
  have hkR : (3 : ℝ) * k ≤ V.card := by exact_mod_cast hk
  have hp0 : 0 ≤ (k : ℝ) / V.card := div_nonneg (Nat.cast_nonneg _) hn.le
  have hp1 : (k : ℝ) / V.card ≤ 1 / 3 := by
    apply (div_le_iff₀ hn).mpr
    linarith
  have hent := binaryEntropy_monoOn ⟨hp0, by linarith⟩
    (by norm_num : (1 / 3 : ℝ) ∈ Set.Icc 0 (1 / 2)) hp1
  have hc : ((sumsAtSize a V k).card : ℝ) ≤ (V.card.choose k : ℝ) := by
    exact_mod_cast (show (sumsAtSize a V k).card ≤ V.card.choose k from
      Finset.card_image_le.trans (Finset.card_powersetCard _ _).le)
  apply hc.trans ((choose_entropy_bounds V.card k hkV).2.trans ?_)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  exact mul_le_mul_of_nonneg_left hent hn.le

/-- Once a block supplies enough distinct sums, the size selected by
pigeonhole lies strictly above one third of that block and at most one half.
These are exactly the guesses used by the representation trial. -/
theorem exists_representative_size_range (a : ι → ℤ) (V : Finset ι)
    (hV : 0 < V.card)
    (hcount : (2 : ℝ) ^ ((V.card : ℝ) * binaryEntropy (1 / 3)) <
      (distinctSumCount a V : ℝ) / (V.card + 1)) :
    ∃ k, V.card < 3 * k ∧ k ≤ V.card / 2 ∧
      (distinctSumCount a V : ℝ) / (V.card + 1) ≤ (sumsAtSize a V k).card := by
  obtain ⟨k, hk, hN⟩ := exists_representative_size a V
  rw [two_pow_card_sub_deficiency] at hN
  refine ⟨k, ?_, hk, hN⟩
  by_contra hsmall
  have hbound := sumsAtSize_card_le_third_entropy a V hV (by omega : 3 * k ≤ V.card)
  linarith

/-- The small-deficiency regime eventually excludes the lower third. The
margin `1/1500` is absolute, so this assertion is uniform in the weights. -/
theorem eventually_small_deficiency_size_range :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ (a : ι → ℤ) (V : Finset ι), V.card = m →
      deficiency a V ≤ (33 / 500 : ℝ) * m →
      ∃ k, V.card < 3 * k ∧ k ≤ V.card / 2 ∧
        (2 : ℝ) ^ ((V.card : ℝ) - deficiency a V) / (V.card + 1) ≤
          (sumsAtSize a V k).card := by
  filter_upwards [polynomial_absorption 2 (by norm_num : (0 : ℝ) < 1 / 1500),
    Filter.eventually_ge_atTop 3] with m hpoly hm
  intro a V hcard hd
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hlinear : (m : ℝ) + 1 < (m : ℝ) ^ 2 := by nlinarith
  have hden : (m : ℝ) + 1 < (2 : ℝ) ^ ((1 / 1500 : ℝ) * m) :=
    hlinear.trans_le hpoly
  have hgap : binaryEntropy (1 / 3) + (1 / 1500 : ℝ) < 467 / 500 := by
    linarith [binaryEntropy_third_lt]
  have hexp : (m : ℝ) * binaryEntropy (1 / 3) + (1 / 1500 : ℝ) * m <
      (m : ℝ) - deficiency a V := by
    nlinarith
  have hcount : (2 : ℝ) ^ ((V.card : ℝ) * binaryEntropy (1 / 3)) <
      (distinctSumCount a V : ℝ) / (V.card + 1) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < V.card + 1)).mpr
    rw [← two_pow_card_sub_deficiency, hcard]
    calc
      (2 : ℝ) ^ ((m : ℝ) * binaryEntropy (1 / 3)) * ((m : ℝ) + 1)
          < (2 : ℝ) ^ ((m : ℝ) * binaryEntropy (1 / 3)) *
              (2 : ℝ) ^ ((1 / 1500 : ℝ) * m) :=
        mul_lt_mul_of_pos_left hden (Real.rpow_pos_of_pos (by norm_num) _)
      _ = (2 : ℝ) ^ ((m : ℝ) * binaryEntropy (1 / 3) +
          (1 / 1500 : ℝ) * m) := (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ < (2 : ℝ) ^ ((m : ℝ) - deficiency a V) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  obtain ⟨k, hlow, hhigh, hmany⟩ := exists_representative_size_range a V
    (by omega) hcount
  refine ⟨k, hlow, hhigh, ?_⟩
  rwa [two_pow_card_sub_deficiency]

/-- The manuscript's absolute threshold makes `tau = .0078n` at most
`.066s` for every size-`s` mixer half; the floor in `m` is included. -/
theorem half_mixer_deficiency_threshold {n : ℕ} (hn : 2200 ≤ n) :
    (39 / 5000 : ℝ) * n ≤ (33 / 500 : ℝ) * (mixerSize n / 2 : ℕ) := by
  have hdiv : mixerSize n / 2 = 4 * (3 * n / 100) := by
    simp only [mixerSize]
    omega
  have hl := (mixerSize_bounds n).1
  have hnR : (2200 : ℝ) ≤ n := by exact_mod_cast hn
  rw [hdiv]
  simp only [mixerSize, Nat.cast_mul, Nat.cast_ofNat] at hl ⊢
  linarith

end LowSpaceSubsetSum

end OAI
