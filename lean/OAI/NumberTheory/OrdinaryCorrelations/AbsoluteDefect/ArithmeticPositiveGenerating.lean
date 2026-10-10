import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Count

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

theorem arithmetic_positive_generating (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    {N : ℕ} (hN : 0<N) {z : ℝ} (hz : 1≤z) :
    arithmeticGenerating P N z ≤ ∏p : P, (1+(z-1)*(p:ℝ)⁻¹) := by
  rw [arithmetic_expansion P hP]
  have hex := polynomial_expansion (fun p : P => (p:ℝ)⁻¹) z
  have he : (∏p : P, (1+(z-1)*(p:ℝ)⁻¹)) =
      ∑t∈(univ : Finset P).powerset, (z-1)^t.card * ∏p∈t,(p:ℝ)⁻¹ := by
    convert hex using 1
    apply prod_congr rfl
    intro p hp
    ring
  rw [he]
  apply sum_le_sum
  intro t ht
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (sub_nonneg.mpr hz) _)
  have hu := Nat.cast_div_le (α:=ℝ) (m:=N) (n:=∏p∈t,(p:ℕ))
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hh := div_le_div_of_nonneg_right hu hNr.le
  have he' : ((N:ℝ)/(∏p∈t,(p:ℕ):ℕ))/(N:ℝ) = ∏p∈t,(p:ℝ)⁻¹ := by
    rw [Nat.cast_prod, div_div, div_eq_mul_inv]
    simp only [mul_inv_rev, ←mul_assoc, mul_inv_cancel₀ hNr.ne', one_mul,
      prod_inv_distrib]
  rwa [he'] at hh

theorem arithmetic_primeCount_exponential (P : Finset ℕ)
    (hP : ∀p∈P,Nat.Prime p) {N : ℕ} (hN : 0<N) {z : ℝ} (hz : 1≤z) :
    ∑ n∈Icc 1 N, z^((P.filter (fun p => p∣n)).card) ≤
      (N:ℝ)*Real.exp ((z-1)*(∑p∈P,(p:ℝ)⁻¹)) := by
  have hh := arithmetic_positive_generating P hP hN hz
  have he : (∏p : P,(1+(z-1)*(p:ℝ)⁻¹)) ≤
      Real.exp ((z-1)*(∑p∈P,(p:ℝ)⁻¹)) := by
    calc
      _ ≤ ∏p : P, Real.exp ((z-1)*(p:ℝ)⁻¹) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have : 0 ≤ z-1 := sub_nonneg.mpr hz
          positivity
        · intro p hp
          simpa only [add_comm] using Real.add_one_le_exp ((z-1)*(p:ℝ)⁻¹)
      _ = _ := by rw [←Real.exp_sum, ←mul_sum, sum_coe_sort P (fun p : ℕ => (p:ℝ)⁻¹)]
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hf : arithmeticGenerating P N z =
      (∑n∈Icc 1 N,z^((P.filter (fun p => p∣n)).card))/(N:ℝ) := by
    unfold arithmeticGenerating
    simp only [count_primeBits, div_eq_mul_inv, mul_comm (N:ℝ)⁻¹,
      sum_mul]
  rw [hf] at hh
  exact (div_le_iff₀ hNr).mp (hh.trans he) |>.trans_eq (mul_comm _ _)

end OrdinaryCofactorWeight

end

end OAI
