import OAI.NumberTheory.TwoPoint.Bounds.SieveCutoffScale

namespace OAI

/-! A uniform Goldbach bound for all even targets below one common scale. -/

namespace TwoPointCorrelations

open Filter Problem337

lemma sieve_pair_scale_algebra {C x L l S n : ℝ}
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hL : 0 < L) (hl : 0 < l)
    (hS : 1 ≤ S) (_hn : 0 ≤ n) (hnx : n ≤ 4 * x) (hLl : L ≤ 16 * l) :
    C * n * S / l ^ 2 + x / L ^ 2 ≤ (1024 * C + 1) * x * S / L ^ 2 := by
  have hS0 : 0 ≤ S := by linarith
  have hLsq : L ^ 2 ≤ 256 * l ^ 2 := by nlinarith
  have hratio : 1 / l ^ 2 ≤ 256 / L ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hl) (sq_pos_of_pos hL)).mpr
    nlinarith
  have hnS : C * n * S ≤ 4 * C * x * S := by
    nlinarith [mul_le_mul_of_nonneg_right hnx (mul_nonneg hC hS0)]
  have hxS : x ≤ x * S := by nlinarith
  calc
    _ = (C * n * S) * (1 / l ^ 2) + x / L ^ 2 := by ring
    _ ≤ (4 * C * x * S) * (256 / L ^ 2) + (x * S) / L ^ 2 := by
      apply add_le_add
      · exact mul_le_mul hnS hratio (by positivity) (by positivity)
      · exact div_le_div_of_nonneg_right hxS (sq_nonneg _)
    _ = _ := by ring

theorem sieve_goldbach_pairs_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      1 ≤ x ∧ 1 ≤ Real.log x ∧ ∀ N : ℕ, N ≠ 0 → 2 ∣ N → (N : ℝ) ≤ 4 * x →
        ((PrimePairSieve.primePairs N).card : ℝ) ≤
          C * x * sieveSingularFactor N / Real.log x ^ 2 := by
  obtain ⟨C, hC, hpairs⟩ := sieve_goldbach_pairs_finite
  refine ⟨1024 * C + 1, by positivity, ?_⟩
  filter_upwards [sieve_power_cutoff_eventually (8 * (halaszMertensConstant + Real.log 2))]
    with x hx
  obtain ⟨hx1, hxlog, hz2, hzscale, hzlog, hzerr⟩ := hx
  refine ⟨hx1, hxlog, ?_⟩
  intro N hN0 hN hNx
  let z := ⌊x ^ (1 / 8 : ℝ)⌋₊
  have hzlogpos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have he := hpairs N z hN hN0 hz2 hzscale
  have halg := sieve_pair_scale_algebra hC.le (by linarith : 0 ≤ x)
    (by linarith : 0 < Real.log x) hzlogpos (sieve_singular_factor_one_le N)
    (Nat.cast_nonneg N) hNx hzlog
  linarith

end TwoPointCorrelations

end OAI
