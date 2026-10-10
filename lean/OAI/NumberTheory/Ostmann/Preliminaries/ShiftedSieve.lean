import OAI.NumberTheory.Ostmann.Preliminaries.CountSquare
import OAI.NumberTheory.Ostmann.Preliminaries.SiftedBound
import OAI.NumberTheory.Ostmann.Preliminaries.SiftedInterpolation
import OAI.NumberTheory.Ostmann.Preliminaries.SiftedScales

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open Filter
open Ostmann.SiftedWeights

theorem eventually_countA_log_power (d : Ostmann.Decomposition) (j : ℕ) (hj : 0 < j) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      (countUpTo d.A x : ℝ) ≤ C*x/(Real.log (x : ℝ))^j := by
  classical
  apply dyadic_bound_to_log_bound (fun x => (countUpTo d.A x : ℝ))
    (fun x y h => by
      change (countUpTo d.A x : ℝ) ≤ (countUpTo d.A y : ℝ)
      exact_mod_cast countUpTo_mono d.A h)
    (fun _ => Nat.cast_nonneg _) j
  obtain ⟨K, C, hjK, hC, hsieve⟩ := exists_finite_shift_sieve d j
  let a₀ : ℝ := Real.log 2/(20*(j : ℝ))
  have ha₀ : 0 < a₀ := div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hapow : 0 < a₀^j := pow_pos ha₀ j
  refine ⟨C/a₀^j+1, by positivity, ?_⟩
  filter_upwards [eventually_sieve_scales j K hj, eventually_boundary_negligible j d.cutoff,
    eventually_ge_atTop 1] with n hscale hboundary hn1
  let Q := sieveLevel n
  let R := smallPrimeCutoff j n
  let U := tailElements d.A (Q+d.cutoff) (Q^2)
  have hQsq : Q^2 = 4^n := by
    dsimp [Q, sieveLevel]
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have hQsqR : (Q : ℝ)^2 = (4 : ℝ)^n := by exact_mod_cast hQsq
  have huc := hsieve R Q hscale.1 hscale.2.1 hscale.2.2.1 U
    (fun a ha => (mem_tailElements.mp ha).1)
    (fun a ha => (mem_tailElements.mp ha).2.2)
    (fun a ha => (mem_tailElements.mp ha).2.1)
  have hRlog : 0 < Real.log (R : ℝ) := Real.log_pos (by
    have hR : 2 ≤ R := (le_max_right K 2).trans hscale.1
    exact_mod_cast (show 1 < R by omega))
  have hnp : 0 < (n : ℝ)^j := pow_pos (by exact_mod_cast hn1) j
  have hlog : a₀*(n : ℝ) ≤ Real.log (R : ℝ) := by
    have h := hscale.2.2.2
    change Real.log (Q : ℝ)/(20*(j : ℝ)) ≤ Real.log (R : ℝ) at h
    have he : Real.log (Q : ℝ)/(20*(j : ℝ)) = a₀*(n : ℝ) := by
      simp only [Q, sieveLevel, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      dsimp [a₀]
      ring
    rwa [he] at h
  have hlogpow := pow_le_pow_left₀ (mul_nonneg ha₀.le (Nat.cast_nonneg n)) hlog j
  rw [mul_pow] at hlogpow
  have hupper := (le_div_iff₀ (pow_pos hRlog j)).mp huc
  rw [hQsqR] at hupper
  have hweighted := (mul_le_mul_of_nonneg_left hlogpow (Nat.cast_nonneg U.card)).trans hupper
  have hUbound : (U.card : ℝ) ≤ (C/a₀^j)*(4 : ℝ)^n/(n : ℝ)^j := by
    apply (le_div_iff₀ hnp).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hapow).mpr
    nlinarith
  have hrestore : (countUpTo d.A (4^n) : ℝ) ≤ (U.card : ℝ)+((Q : ℝ)+d.cutoff+1) := by
    have h : countUpTo d.A (Q^2) ≤ U.card+(Q+d.cutoff+1) :=
      countUpTo_le_tail_card d.A (Q+d.cutoff) (Q^2)
    rw [hQsq] at h
    exact_mod_cast h
  have hb : (Q : ℝ)+d.cutoff+1 ≤ (4 : ℝ)^n/(n : ℝ)^j := by
    simpa only [Q, sieveLevel, Nat.cast_pow, Nat.cast_ofNat] using hboundary
  calc
    (countUpTo d.A (4^n) : ℝ) ≤ (U.card : ℝ)+((Q : ℝ)+d.cutoff+1) := hrestore
    _ ≤ (C/a₀^j)*(4 : ℝ)^n/(n : ℝ)^j + (4 : ℝ)^n/(n : ℝ)^j := add_le_add hUbound hb
    _ = (C/a₀^j+1)*(4 : ℝ)^n/(n : ℝ)^j := by ring

theorem eventually_countB_log_power (d : Ostmann.Decomposition) (j : ℕ) (hj : 0 < j) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      (countUpTo d.B x : ℝ) ≤ C*x/(Real.log (x : ℝ))^j :=
  eventually_countA_log_power d.swap j hj

end Ostmann.Preliminaries

end OAI
