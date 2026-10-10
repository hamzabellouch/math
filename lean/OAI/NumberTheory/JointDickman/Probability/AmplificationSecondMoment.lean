import OAI.NumberTheory.JointDickman.Probability.OrientedMoments
import OAI.NumberTheory.JointDickman.Probability.NoChangeMoment

namespace OAI

/-! # The amplification second moment in the independent-prime model -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- Both actual fair splits are good with probability O(B^{-2}). The bound
uses the published upper sieve and prime reciprocal Mertens input. -/
theorem amplification_second_moment_probability
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      twoSiteSplitProbability (auxiliaryPrimes B) (bothAmplificationSplitsGood B L T τ C) ≤
        K / (B : ℝ)^2 := by
  obtain ⟨K₁, hK₁, hf⟩ := first_oriented_probability_sum hFord hM
  obtain ⟨K₂, hK₂, hs⟩ := second_oriented_probability_sum hFord hM
  obtain ⟨K₀, hK₀, hn⟩ := no_change_probability_small hFord hM
  intro L τ C
  refine ⟨K₀ + 2 * (K₁ + K₂) * (2 : ℝ)^(4 * C), by positivity, ?_⟩
  filter_upwards [hf, hs, hn L τ C, auxiliaryRatio_tendsto.eventually_ge_atTop 1,
    eventually_gt_atTop 1] with B hfb hsb hnb hratio hB
  intro T hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hlog : 0 < Real.log (auxiliaryCutoff B) := by
    rw [log_auxiliaryCutoff]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hB))
  have hLB : Real.log (auxiliaryCutoff B) ≤ (B : ℝ) := by
    have hh : 1 ≤ (B : ℝ) / Real.log (auxiliaryCutoff B) := by
      simpa only [auxiliaryRatio, log_auxiliaryCutoff] using hratio
    have hh' := (le_div_iff₀ hlog).mp hh
    simpa only [one_mul] using hh'
  obtain ⟨N, _, hcap, hcap'⟩ := dyadic_cover_endpoint hlog
    (show Real.log (auxiliaryCutoff B) ≤ 4 * (B : ℝ) by linarith only [hLB, hB0])
  have hi : ∀ i ∈ Icc 1 N, primeTailEndpoint B i ≤ 8 * B := by
    intro i hi
    have hp : (2 : ℝ)^i ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) (mem_Icc.mp hi).2
    exact (mul_le_mul_of_nonneg_right hp hlog.le).trans (by linarith only [hcap'])
  have hfirst := hfb L T τ C (Icc 1 N) hT hTsize hi
  have hsecond := hsb L T τ C (Icc 1 N) hT hTsize hi
  have hno := hnb T hT hTsize
  calc
    _ ≤ twoSiteSplitProbability (auxiliaryPrimes B)
          (fun x => bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x) +
        2 * ∑ i ∈ Icc 1 N,
          (twoSiteSplitProbability (auxiliaryPrimes B)
            (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false) +
           twoSiteSplitProbability (auxiliaryPrimes B)
            (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true)) :=
      amplification_orientation_cover L T τ C hB hcap
    _ ≤ K₀ / (B : ℝ)^2 +
        2 * (K₁ * (2 : ℝ)^(4 * C) / (B : ℝ)^2 + K₂ * (2 : ℝ)^(4 * C) / (B : ℝ)^2) := by
      rw [sum_add_distrib]
      exact add_le_add hno (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num))
    _ = _ := by ring

end JointDickman

end OAI
