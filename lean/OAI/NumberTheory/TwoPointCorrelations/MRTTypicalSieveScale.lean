import OAI.NumberTheory.TwoPointCorrelations.MRTMissingBandSieve
import OAI.NumberTheory.TwoPointCorrelations.SieveBoundaryScale

namespace OAI

/-! Uniform finite-interval error in the sieve for MRT's prime bands.
The prime mass uses the proved Mertens theorem; the remaining errors are
the explicit Bonferroni and CRT boundary errors. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma mrt_exponential_sieve_tail (M L : ℝ) (j : ℕ) (hL : 1 ≤ L)
    (hM : M ≤ 5 * Real.log L) (hj : 220 * Real.log L ≤ (j : ℝ)) :
    Real.exp (2 * M) / (2 : ℝ) ^ j ≤ L ^ (-100 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hh
    linarith
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num),
    ← Real.exp_sub, Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have horder : 110 * Real.log L ≤ (j : ℝ) * Real.log 2 := by
    calc
      _ = (220 * Real.log L) * (1 / 2 : ℝ) := by ring
      _ ≤ (j : ℝ) * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hj (by norm_num)
      _ ≤ (j : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg j)
  nlinarith

lemma mrt_prime_band_card_le (P Q : ℝ) (hQ : 0 ≤ Q) :
    ((mrtPrimeBand P Q).card : ℝ) ≤ Q := by
  have hc : (mrtPrimeBand P Q).card ≤ (sievePrimesUpTo Q).card :=
    card_le_card sdiff_subset
  exact (show ((mrtPrimeBand P Q).card : ℝ) ≤ (sievePrimesUpTo Q).card by
    exact_mod_cast hc).trans (sievePrimesUpTo_card_le Q hQ)

/-- A single prime band has its Mertens main term, uniformly in the
interval's starting point, plus an error smaller than `2 L^-100`. -/
theorem mrt_eventually_missing_band : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      Q ≤ Real.exp (L ^ (99 / 100 : ℝ)) →
      ∀ (A N : ℕ) [NeZero N],
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids (mrtPrimeBand P Q) (A + j.val)) ≤
        C * Real.log P / Real.log Q + 2 * L ^ (-100 : ℝ) := by
  obtain ⟨C, hC, hband⟩ := mrt_missing_band_probability
  obtain ⟨CM, _, hmass⟩ := primeReciprocalInput.rough_scale
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1), hmass,
    eventually_sieve_boundary_cost 222 1 (by norm_num) (by norm_num)] with
      L hL hmass hboundary
  intro P Q hP hPQ hQmax A N _ hN
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hlog : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hL
  let r : ℕ := ⌈110 * Real.log L⌉₊
  have hrlo : 110 * Real.log L ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < 110 * Real.log L + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hR : ((2 * r : ℕ) : ℝ) ≤ 222 * Real.log L := by
    push_cast
    nlinarith
  have hj : 220 * Real.log L ≤ ((2 * r + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hsub : mrtPrimeBand P Q ⊆
      sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))) :=
    sdiff_subset.trans (mrt_sievePrimesUpTo_mono hQmax)
  have hM : (∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) ≤ 5 * Real.log L := by
    calc
      _ ≤ ∑ p ∈ sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))), 1 / (p : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
      _ ≤ (5 / 4 : ℝ) * Real.log L := hmass.2
      _ ≤ _ := by nlinarith
  have ht := mrt_exponential_sieve_tail _ L (2 * r + 1) hL1 hM hj
  have hb := hboundary Q ((mrtPrimeBand P Q).card : ℝ) N (2 * r) hQ0
    (Nat.cast_nonneg _) (mrt_prime_band_card_le P Q hQ0) hQmax hR hN
  have hh := hband P Q hP hPQ A N r
  simp only [one_div] at hb hh ht
  linarith

/-- The uniform band errors add over the actual family of bands; the
main term is the sum of their logarithmic endpoint ratios. -/
theorem mrt_eventually_atypical_family : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (ι : Type*) [Fintype ι] (P Q : ι → ℝ),
      (∀ i, 2 ≤ P i) → (∀ i, P i ≤ Q i) →
      (∀ i, Q i ≤ Real.exp (L ^ (99 / 100 : ℝ))) →
      ∀ (A N : ℕ) [NeZero N],
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun j => ¬mrtTypical univ (fun i => mrtPrimeBand (P i) (Q i)) (A + j.val)) ≤
        C * ∑ i, Real.log (P i) / Real.log (Q i) +
          2 * Fintype.card ι * L ^ (-100 : ℝ) := by
  obtain ⟨C, hC, hband⟩ := mrt_eventually_missing_band
  refine ⟨C, hC, ?_⟩
  filter_upwards [hband] with L hband
  intro ι _ P Q hP hPQ hQ A N _ hN
  calc
    _ ≤ ∑ i, (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids (mrtPrimeBand (P i) (Q i)) (A + j.val)) :=
      mrtTypical_missing_union _ _ _
    _ ≤ ∑ i, (C * Real.log (P i) / Real.log (Q i) + 2 * L ^ (-100 : ℝ)) :=
      sum_le_sum (fun i _ => hband (P i) (Q i) (hP i) (hPQ i) (hQ i) A N hN)
    _ = _ := by
      simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      rw [mul_sum]
      congr 1
      · apply sum_congr rfl
        intro i _
        ring
      · ring

end TwoPointCorrelations

end OAI
