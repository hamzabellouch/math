import OAI.NumberTheory.TwoPoint.Halasz.HalaszCountMonotone
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! An elementary supply of primes in a fixed multiplicative interval.
Chebyshev's bounds suffice; no prime number theorem is needed here. -/
namespace TwoPointCorrelations

open Finset Filter
open scoped Classical Topology

lemma halasz_theta_eventually_lower :
    ∀ᶠ x : ℝ in atTop, x/4≤Chebyshev.theta x := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hlog := Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ)<1/32)
  have hshift : Tendsto (fun x : ℝ => x+2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hroot : Tendsto Real.sqrt atTop atTop := Real.tendsto_sqrt_atTop
  have hlog2 : (1:ℝ)/2≤Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  filter_upwards [hshift.eventually hlog,hroot.eventually (eventually_ge_atTop (16*|C|)),
    eventually_ge_atTop (4:ℝ)] with x hl hs hx
  have hx0 : 0≤x := by linarith
  have hxs := Real.sq_sqrt hx0
  have hlogx : Real.log (x+2)≤x/16 := by
    change ‖Real.log (x+2)‖≤(1/32:ℝ)*‖x+2‖ at hl
    rw [Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith)),
      abs_of_nonneg (by linarith : 0≤x+2)] at hl
    have ha := le_abs_self (Real.log (x+2))
    linarith
  have hsC : C*Real.sqrt x≤x/16 := by
    have hm := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg x)
    have hc := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg x)
    nlinarith only [hm,hc,hxs]
  have hpsi := Chebyshev.psi_ge' hx0
  have htheta := hC x
  have hhalf := mul_le_mul_of_nonneg_left hlog2 (by linarith : 0≤x-1)
  linarith

lemma halasz_theta_upper {x : ℝ} (hx : 0≤x) : Chebyshev.theta x≤2*x := by
  have hl : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have h4 : Real.log 4≤2 := by
    have he : Real.log 4=2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    linarith
  exact (Chebyshev.theta_le_log4_mul_x hx).trans (mul_le_mul_of_nonneg_right h4 hx)

def halaszPrimeSupply (R : ℕ) : Finset ℕ := Nat.primesLE (16*R)\Nat.primesLE R

lemma halasz_prime_supply_mem {R p : ℕ} (hp : p∈halaszPrimeSupply R) :
    p.Prime ∧ R<p ∧ p≤16*R := by
  have h := mem_sdiff.mp hp
  have ha := Nat.mem_primesLE.mp h.1
  have hb : ¬p≤R := by intro he; exact h.2 (Nat.mem_primesLE.mpr ⟨he,ha.2⟩)
  exact ⟨ha.2,by omega,ha.1⟩

lemma halasz_prime_supply_mass (R : ℕ) :
    (∑ p∈halaszPrimeSupply R, Real.log (p:ℝ)) =
      Chebyshev.theta (16*(R:ℝ))-Chebyshev.theta (R:ℝ) := by
  rw [show 16*(R:ℝ)=((16*R:ℕ):ℝ) by push_cast; rfl,
    Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE_log]
  apply (eq_sub_iff_add_eq).mpr
  exact sum_sdiff (f := fun p : ℕ => Real.log (p:ℝ))
    (Nat.primesLE_mono (by omega : R≤16*R))

theorem halasz_prime_supply_card :
    ∀ᶠ R : ℕ in atTop, Real.sqrt (R:ℝ)≤(halaszPrimeSupply R).card := by
  have ht : Tendsto (fun R : ℕ => 16*(R:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<16)
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).bound
    (by norm_num : (0:ℝ)<1/4)
  filter_upwards [ht.eventually halasz_theta_eventually_lower,ht.eventually hlog,
    eventually_ge_atTop (1:ℕ)] with R htheta hl hR
  have hR0 : (0:ℝ)<R := by exact_mod_cast (by omega : 0<R)
  have hs0 : 0<Real.sqrt (R:ℝ) := Real.sqrt_pos.mpr hR0
  have hlogBound : Real.log (16*(R:ℝ))≤Real.sqrt (R:ℝ) := by
    change ‖Real.log (16*(R:ℝ))‖≤(1/4:ℝ)*‖(16*(R:ℝ))^(1/2:ℝ)‖ at hl
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg
      (Real.rpow_nonneg (by positivity) _),← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by norm_num : (0:ℝ)≤16)] at hl
    norm_num at hl
    linarith [le_abs_self (Real.log (16*(R:ℝ)))]
  have hmass : 2*(R:ℝ)≤∑ p∈halaszPrimeSupply R, Real.log (p:ℝ) := by
    rw [halasz_prime_supply_mass]
    have hu := halasz_theta_upper hR0.le
    linarith
  have hsum : (∑ p∈halaszPrimeSupply R, Real.log (p:ℝ)) ≤
      ((halaszPrimeSupply R).card:ℝ)*Real.sqrt (R:ℝ) := by
    calc
      _ ≤ ∑ _p∈halaszPrimeSupply R, Real.sqrt (R:ℝ) := by
        apply sum_le_sum
        intro p hp
        have h := halasz_prime_supply_mem hp
        exact (Real.log_le_log (by exact_mod_cast h.1.pos)
          (by exact_mod_cast h.2.2)).trans hlogBound
      _ = _ := by simp
  have hs := Real.sq_sqrt hR0.le
  nlinarith

end TwoPointCorrelations

end OAI
