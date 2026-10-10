import Mathlib.Analysis.MeanInequalities

namespace OAI

/-! # A constant shift in a weighted integral moment -/

namespace Ostmann

open scoped BigOperators

/-- Minkowski for a countable weighted moment, stated without any measure
construction. The weights may have infinite support. -/
theorem weighted_moment_shift {ι : Type*} (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (b : ℝ) (hb : 0 ≤ b)
    (k : ℕ) (hk : 0 < k) (hws : Summable w)
    (hfs : Summable (fun i => w i * f i ^ k)) :
    Summable (fun i => w i * (f i + b) ^ k) ∧
      (∑' i, w i * (f i + b) ^ k) ≤
        ((∑' i, w i * f i ^ k) ^ (1 / (k : ℝ)) +
          b * (∑' i, w i) ^ (1 / (k : ℝ))) ^ k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let u : ι → ℝ := fun i => w i ^ (1 / (k : ℝ))
  have hu (i : ι) : 0 ≤ u i := Real.rpow_nonneg (hw i) _
  have hup (i : ι) : u i ^ k = w i := by
    simpa only [u, one_div] using Real.rpow_inv_natCast_pow (hw i) hk.ne'
  have hfa (i : ι) : (u i * f i) ^ (k : ℝ) = w i * f i ^ k := by
    rw [Real.rpow_natCast, mul_pow, hup]
  have hba (i : ι) : (u i * b) ^ (k : ℝ) = w i * b ^ k := by
    rw [Real.rpow_natCast, mul_pow, hup]
  have hsa (i : ι) : (u i * f i + u i * b) ^ (k : ℝ) = w i * (f i + b) ^ k := by
    rw [← mul_add, Real.rpow_natCast, mul_pow, hup]
  have hsumf : Summable (fun i => (u i * f i) ^ (k : ℝ)) := by simpa only [hfa] using hfs
  have hsumb : Summable (fun i => (u i * b) ^ (k : ℝ)) := by
    simpa only [hba] using hws.mul_right (b ^ k)
  obtain ⟨hs, hi⟩ := Real.Lp_add_le_tsum_of_nonneg hk1
    (fun i => mul_nonneg (hu i) (hf i)) (fun i => mul_nonneg (hu i) hb) hsumf hsumb
  simp only [hsa, hfa, hba] at hs hi
  have hI : 0 ≤ ∑' i, w i * (f i + b) ^ k :=
    tsum_nonneg (fun i => mul_nonneg (hw i) (pow_nonneg (add_nonneg (hf i) hb) _))
  have hconst : (∑' i, w i * b ^ k) ^ (1 / (k : ℝ)) =
      b * (∑' i, w i) ^ (1 / (k : ℝ)) := by
    rw [tsum_mul_right, Real.mul_rpow (tsum_nonneg hw) (pow_nonneg hb k),
      one_div, Real.pow_rpow_inv_natCast hb hk.ne', mul_comm]
  rw [hconst] at hi
  refine ⟨hs, ?_⟩
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hi k
  rw [one_div, Real.rpow_inv_natCast_pow hI hk.ne'] at hh
  simpa only [one_div] using hh

end Ostmann

end OAI
