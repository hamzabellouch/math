import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryLogarithms
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeIntervalSums

namespace OAI

/-! # Mertens sums at the prefix scales used by regularity -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliaryCutoff_le_exp_rpow {c g : ℝ} (hc : 0 < c) (hg : 0 < g) :
    ∀ᶠ B : ℕ in atTop, (auxiliaryCutoff B : ℝ) ≤ Real.exp (c * (B : ℝ) ^ g) := by
  have hlim : Tendsto (fun B : ℕ => (1000 / c) * (Real.log B / (B : ℝ) ^ g)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((isLittleO_log_rpow_atTop hg).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul (1000 / c)
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hpow : 0 < (B : ℝ) ^ g := Real.rpow_pos_of_pos hB0 g
  have hsmall' : 1000 * Real.log B ≤ c * (B : ℝ) ^ g := by
    have hh : (1000 * Real.log B) / (c * (B : ℝ) ^ g) ≤ 1 := by
      convert hsmall using 1; field_simp
    exact (div_le_one (mul_pos hc hpow)).mp hh
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast pow_pos (by omega : 0 < B) 1000
  calc
    _ = Real.exp (Real.log (auxiliaryCutoff B)) := (Real.exp_log hP).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [log_auxiliaryCutoff] using hsmall')

/-- Both interior prefixes and the full fixed exponential cutoff have
normalized reciprocal-prime mass g; the endpoint multiplier c contributes
only a bounded logarithm. -/
theorem regularity_prefix_prime_sum_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c g : ℝ}
    (hc : 0 < c) (hg : 0 < g) :
    Tendsto (fun B : ℕ =>
      (∑ p ∈ largePrimeSet (Real.exp (c * (B : ℝ) ^ g)) (auxiliaryCutoff B), 1 / (p : ℝ)) /
        auxiliaryLogLength B) atTop (𝓝 g) := by
  obtain ⟨M, hrem⟩ := primeReciprocalSum_remainder_tendsto hM
  have hpow : Tendsto (fun B : ℕ => c * (B : ℝ) ^ g) atTop atTop :=
    ((tendsto_rpow_atTop hg).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have hupper := Real.tendsto_exp_atTop.comp hpow
  have hcut : Tendsto (fun B : ℕ => (auxiliaryCutoff B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto
  have herr : Tendsto (fun B : ℕ =>
      ((primeReciprocalSum (Real.exp (c * (B : ℝ) ^ g)) - Real.log (Real.log (Real.exp (c * (B : ℝ) ^ g)))) -
        (primeReciprocalSum (auxiliaryCutoff B) - Real.log (Real.log (auxiliaryCutoff B)))) /
          auxiliaryLogLength B) atTop (𝓝 0) :=
    ((hrem.comp hupper).sub (hrem.comp hcut)).div_atTop auxiliaryLogLength_tendsto
  have hconst : Tendsto (fun B : ℕ => Real.log c / auxiliaryLogLength B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop auxiliaryLogLength_tendsto
  have hmain := (hconst.add (log_div_auxiliaryLogLength_tendsto.const_mul g)).sub
    logLogCutoff_div_auxiliaryLogLength_tendsto_zero
  have h := herr.add hmain
  norm_num only [zero_add, mul_one, sub_zero] at h
  apply h.congr'
  filter_upwards [auxiliaryCutoff_le_exp_rpow hc hg, eventually_gt_atTop 1] with B hPY hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  rw [largePrimeSet_reciprocal_eq (Nat.cast_nonneg _) hPY, Real.log_exp,
    Real.log_mul hc.ne' (Real.rpow_pos_of_pos hB0 g).ne', Real.log_rpow hB0]
  ring

end JointDickman

end OAI
