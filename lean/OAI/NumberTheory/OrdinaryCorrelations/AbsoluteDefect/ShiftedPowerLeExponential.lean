import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ArithmeticPositiveGenerating

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryCofactorWeight
open Finset

theorem shifted_power_le_exponential (w k : ℕ) {a : ℝ} (ha : 0<a) :
    ((w+k:ℕ):ℝ)^k ≤ (k.factorial:ℝ)/a^k * Real.exp (a*k) *
      (Real.exp a)^w := by
  have hx : 0 ≤ a*((w+k:ℕ):ℝ) := by positivity
  have hf : 0 < (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hp := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (a*((w+k:ℕ):ℝ)) hx k)
  rw [mul_pow] at hp
  have he : Real.exp (a*((w+k:ℕ):ℝ)) = Real.exp (a*k)*(Real.exp a)^w := by
    rw [Nat.cast_add, mul_add, Real.exp_add, mul_comm a (w:ℝ), Real.exp_nat_mul]
    ring
  rw [he] at hp
  have hh := (le_div_iff₀ (pow_pos ha k)).mpr (show
    ((w+k:ℕ):ℝ)^k*a^k ≤ Real.exp (a*k)*(Real.exp a)^w*(k.factorial:ℝ) by
      simpa only [mul_comm (((w+k:ℕ):ℝ)^k) (a^k)] using hp)
  calc
    _ ≤ Real.exp (a*k)*(Real.exp a)^w*(k.factorial:ℝ)/a^k := hh
    _ = _ := by ring

theorem arithmetic_shifted_primeCount_moment (P : Finset ℕ)
    (hP : ∀p∈P,Nat.Prime p) {N : ℕ} (hN : 0<N) (k : ℕ)
    {a : ℝ} (ha : 0<a) :
    ∑n∈Icc 1 N, (((P.filter (fun p => p∣n)).card+k:ℕ):ℝ)^k ≤
      (N:ℝ)*((k.factorial:ℝ)/a^k)*
        Real.exp (a*k+(Real.exp a-1)*(∑p∈P,(p:ℝ)⁻¹)) := by
  have hz : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha.le
  have hb := arithmetic_primeCount_exponential P hP hN hz
  calc
    _ ≤ ∑n∈Icc 1 N, ((k.factorial:ℝ)/a^k * Real.exp (a*k)) *
        (Real.exp a)^((P.filter (fun p => p∣n)).card) := by
      apply sum_le_sum
      intro n hn
      exact shifted_power_le_exponential _ k ha
    _ = ((k.factorial:ℝ)/a^k * Real.exp (a*k)) *
        ∑n∈Icc 1 N, (Real.exp a)^((P.filter (fun p => p∣n)).card) := by rw [mul_sum]
    _ ≤ ((k.factorial:ℝ)/a^k * Real.exp (a*k)) *
        ((N:ℝ)*Real.exp ((Real.exp a-1)*(∑p∈P,(p:ℝ)⁻¹))) := by
      apply mul_le_mul_of_nonneg_left hb
      positivity
    _ = _ := by rw [Real.exp_add]; ring

end OrdinaryCofactorWeight

end

end OAI
