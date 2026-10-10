import OAI.NumberTheory.JointDickman.Arithmetic.SingleSieveRemainder

namespace OAI

/-! # The one-coefficient mean bound from the published upper sieve -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem single_coefficient_mean_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ u v : ℕ, u ≤ v →
      Real.exp (δ * B) ≤ (v : ℝ) - u →
      (∑ n ∈ Ico u v, coefficientWeight B n) ≤ C * ((v : ℝ) - u) := by
  obtain ⟨C, hC, hbound⟩ := single_coefficient_exp_moment hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C + 1, by linarith only [hC], ?_⟩
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8),
    single_coefficient_remainder_power hδ, eventually_gt_atTop 1] with B hcut hrem hB
  intro u v huv hlen
  have hb := hbound B (sieveCutoff (δ / 8) B) u v hB hcut.1 hcut.2.1
    (by linarith only [hcut.2.2.1]) huv ∅ 0 (by norm_num)
  have hm : (∑ n ∈ Ico u v, coefficientWeight B n) ≤ C * ((v : ℝ) - u) +
      singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
    simpa [tiltedCoefficientWeight, singleCoefficientRemainder] using hb
  have hH : 0 ≤ (v : ℝ) - u := (Real.exp_pos _).le.trans hlen
  have hp : (1 : ℝ) ≤ (B : ℝ)^10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ B))
  have he := (hrem _ hlen).trans (div_le_self hH hp)
  nlinarith only [hm, he]

end JointDickman

end OAI
