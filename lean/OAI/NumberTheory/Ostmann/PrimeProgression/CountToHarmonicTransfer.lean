import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicProfile

namespace OAI

open Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open Set
open Ostmann.Dirichlet.PrimeCountAbel (logarithmicIntegral)
namespace Ostmann.Arithmetic.PrimeProgression

theorem harmonic_estimate_of_count_estimate
    (hcount : ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ (M : ℕ) (r : ℤ), 0 < M → IsCoprime r (M : ℤ) →
      (M : ℝ) ≤ Real.exp (c * (Real.log X) ^ (1 / 3 : ℝ)) →
      |((Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes 0 X M r).card : ℝ) -
        logarithmicIntegral X / (M.totient : ℝ)| ≤
        C * X * Real.exp (-c * (Real.log X) ^ (1 / 3 : ℝ))) :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧ ∀ lo hi : ℝ,
      L₀ ≤ lo → lo ≤ hi → hi - lo ≤ 1 → ∀ (N M : ℕ) (r : ℤ),
      ⌊Real.exp hi⌋₊ ≤ N → 0 < M → IsCoprime r (M : ℤ) →
      (M : ℝ) ≤ Real.exp (d * lo ^ (1 / 3 : ℝ)) →
      |harmonicProgression N M (r : ZMod M) lo hi - harmonicIntegral M lo hi| ≤
        K * Real.exp (-d * lo ^ (1 / 3 : ℝ)) := by
  obtain ⟨c, C, X₀, hc, hC, hX₀, hcount⟩ := hcount
  let d := min c 1
  have hd : 0 < d := lt_min hc zero_lt_one
  have hdc : d ≤ c := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  refine ⟨d, 3 * C + 1, max 1 (Real.log X₀), hd, by positivity, le_max_left _ _, ?_⟩
  intro lo hi hlo hlohi hlen N M r hN hM hr hmod
  have hlo1 : 1 ≤ lo := (le_max_left _ _).trans hlo
  have hlopos : 0 < lo := by linarith
  have hXpos : 0 < X₀ := by linarith
  have hXexp : X₀ ≤ Real.exp lo := by
    calc
      X₀ = Real.exp (Real.log X₀) := (Real.exp_log hXpos).symm
      _ ≤ Real.exp lo := Real.exp_le_exp.mpr ((le_max_right _ _).trans hlo)
  have hA : 2 ≤ Real.exp lo := by linarith
  have hprofile : ∀ x ∈ Icc (Real.exp lo) (Real.exp hi),
      |((Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes 0 x M r).card : ℝ) -
          logarithmicIntegral x / (M.totient : ℝ)| ≤
        C * x * Real.exp (-d * (Real.log x) ^ (1 / 3 : ℝ)) := by
    intro x hx
    have hxpos : 0 < x := (Real.exp_pos lo).trans_le hx.1
    have hlog : lo ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx.1
    have hp : lo ^ (1 / 3 : ℝ) ≤ (Real.log x) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow hlopos.le hlog (by norm_num)
    have hp0 : 0 ≤ (Real.log x) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (hlopos.le.trans hlog) _
    have hmodx : (M : ℝ) ≤ Real.exp (c * (Real.log x) ^ (1 / 3 : ℝ)) := by
      apply hmod.trans
      apply Real.exp_le_exp.mpr
      exact mul_le_mul hdc hp (Real.rpow_nonneg hlopos.le _) hc.le
    have h := hcount x (hXexp.trans hx.1) M r hM hr hmodx
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hxpos.le)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hdc hp0]
  have h := harmonicProgression_error_of_exponential_count_error N M r hd.le hC.le
    hlopos hlohi hlen hA hN hprofile
  have hp1 : lo ^ (1 / 3 : ℝ) ≤ lo := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hlo1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hp0 : 0 ≤ lo ^ (1 / 3 : ℝ) := Real.rpow_nonneg hlopos.le _
  have hdp : d * lo ^ (1 / 3 : ℝ) ≤ lo :=
    (mul_le_mul_of_nonneg_right hd1 hp0).trans (by simpa only [one_mul] using hp1)
  have hatom : Real.exp (-lo) ≤ Real.exp (-d * lo ^ (1 / 3 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  apply h.trans
  nlinarith

end Ostmann.Arithmetic.PrimeProgression

end OAI
