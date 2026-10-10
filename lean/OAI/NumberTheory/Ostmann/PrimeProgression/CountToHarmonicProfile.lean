import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicCutoff
import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicFinite

namespace OAI

open Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open Set
open Ostmann.Dirichlet.PrimeCountAbel (logarithmicIntegral)
namespace Ostmann.Arithmetic.PrimeProgression

theorem count_error_profile_uniform {c C lo hi : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hlo : 0 ≤ lo) (M : ℕ) (r : ℤ)
    (herror : ∀ x ∈ Icc (Real.exp lo) (Real.exp hi),
      |((Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes 0 x M r).card : ℝ) -
          logarithmicIntegral x / (M.totient : ℝ)| ≤
        C * x * Real.exp (-c * (Real.log x) ^ (1 / 3 : ℝ))) :
    ∀ x ∈ Icc (Real.exp lo) (Real.exp hi),
      |((Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes 0 x M r).card : ℝ) -
          logarithmicIntegral x / (M.totient : ℝ)| ≤
        (C * Real.exp (-c * lo ^ (1 / 3 : ℝ))) * x := by
  intro x hx
  have hxpos : 0 < x := (Real.exp_pos lo).trans_le hx.1
  have hlog : lo ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx.1
  have hp : lo ^ (1 / 3 : ℝ) ≤ (Real.log x) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hlo hlog (by norm_num)
  have hd : Real.exp (-c * (Real.log x) ^ (1 / 3 : ℝ)) ≤
      Real.exp (-c * lo ^ (1 / 3 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr hc)
  calc
    _ ≤ C * x * Real.exp (-c * (Real.log x) ^ (1 / 3 : ℝ)) := herror x hx
    _ ≤ C * x * Real.exp (-c * lo ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hd (mul_nonneg hC hxpos.le)
    _ = _ := by ring

theorem harmonicProgression_error_of_exponential_count_error (N M : ℕ) (r : ℤ)
    {c C lo hi : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hlo : 0 < lo)
    (hlohi : lo ≤ hi) (hlen : hi - lo ≤ 1) (hA : 2 ≤ Real.exp lo)
    (hN : ⌊Real.exp hi⌋₊ ≤ N)
    (herror : ∀ x ∈ Icc (Real.exp lo) (Real.exp hi),
      |((Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes 0 x M r).card : ℝ) -
          logarithmicIntegral x / (M.totient : ℝ)| ≤
        C * x * Real.exp (-c * (Real.log x) ^ (1 / 3 : ℝ))) :
    |harmonicProgression N M (r : ZMod M) lo hi - harmonicIntegral M lo hi| ≤
      3 * C * Real.exp (-c * lo ^ (1 / 3 : ℝ)) + Real.exp (-lo) := by
  rw [harmonicProgression_cutoff_eq N M (r : ZMod M) lo hi hN]
  have h := harmonicProgression_error_short_interval M r hlo hlohi hlen hA
    (mul_nonneg hC (Real.exp_pos _).le)
    (count_error_profile_uniform hc hC hlo.le M r herror)
  simpa only [mul_assoc] using h

end Ostmann.Arithmetic.PrimeProgression

end OAI
