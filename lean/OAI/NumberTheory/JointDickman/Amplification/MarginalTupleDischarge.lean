import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge
import OAI.NumberTheory.JointDickman.Amplification.ChebyshevDischarge

namespace OAI

/-! # Unconditional control of the finite-bin floor errors -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem largePrimeTupleCount_tendsto_zero (h : ℕ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℝ =>
      (primeTupleCount (largePrimeSet N (N^c)) (h+1) N : ℝ)/N)
      atTop (𝓝 0) :=
  largePrimeTupleCount_tendsto_of_published primeReciprocalMertensInput
    chebyshevPrimeCountingInput h hc hc1

theorem largePrimeTupleCount_scaled_tendsto_zero (h : ℕ) {A c : ℝ}
    (hA : 0 < A) (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun x : ℝ =>
      (primeTupleCount (largePrimeSet x (x^c)) (h+1) (A*x) : ℝ)/(A*x))
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hcount⟩ := chebyshevPrimeCountingInput
  have hrecip := largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1
  have hreciple := hrecip.eventually (eventually_lt_nhds (show -Real.log c < -Real.log c+1 by linarith))
  have hlog : Tendsto (fun x : ℝ => Real.log (x^c)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_rpow_atTop hc)
  have hlim : Tendsto (fun x : ℝ => C*(-Real.log c+1)^h/Real.log (x^c))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hA.le hx.le)
  · filter_upwards [hreciple,(tendsto_rpow_atTop hc).eventually (eventually_ge_atTop (2 : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with x hrecipx hroot hx
    have hsum : 0 ≤ ∑ p ∈ largePrimeSet x (x^c), 1/(p : ℝ) :=
      sum_nonneg (fun _ _ => by positivity)
    have hb := primeTupleCount_bound (P := largePrimeSet x (x^c)) (y := x^c) (N := A*x) h
      (fun p hp => ⟨(Nat.mem_primesLE.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩)
      hC (by linarith : 1 < x^c) (mul_nonneg hA.le hx.le)
      (fun t ht => hcount t (hroot.trans ht))
    have hpow := pow_le_pow_left₀ hsum hrecipx.le h
    have hlogpos : 0 < Real.log (x^c) := Real.log_pos (by linarith)
    have hprod := hb.trans (mul_le_mul_of_nonneg_left hpow
      (by positivity : 0 ≤ C*(A*x)/Real.log (x^c)))
    calc
      _ ≤ ((C*(A*x)/Real.log (x^c))*(-Real.log c+1)^h)/(A*x) :=
        div_le_div_of_nonneg_right hprod (mul_nonneg hA.le hx.le)
      _ = _ := by field_simp

end JointDickman

end OAI
