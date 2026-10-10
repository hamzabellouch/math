import OAI.NumberTheory.JointDickman.Arithmetic.FinitePrimeWeight
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSiteBridge
import OAI.NumberTheory.JointDickman.Arithmetic.RandomRootSieve
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace OAI

/-! # Fair-split Laplace features are finite-prime multiplicative weights -/
namespace JointDickman
open Finset Classical

noncomputable def primeLaplaceFeature (Q : Finset ℕ) (B v : ℝ) (x : Q → Bool) : ℝ :=
  ∏ p : Q, if x p then (1+(p.val : ℝ)^(-v/B))/2 else 1

theorem retainedPrimeProduct_rpow (Q : Finset ℕ)
    (r : ℝ) (y : Q → Bool) :
    (retainedPrimeProduct Q y : ℝ)^r = ∏ p : Q, if y p then (p.val : ℝ)^r else 1 := by
  unfold retainedPrimeProduct
  push_cast
  rw [← Real.finsetProd_rpow]
  · apply prod_congr rfl
    intro p _
    cases y p <;> simp
  · intro p _
    cases y p <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · norm_num
    · exact Nat.cast_nonneg _

theorem fairSplitAverage_laplace (Q : Finset ℕ)
    (B v : ℝ) (x : Q → Bool) :
    fairSplitAverage x (fun y => (retainedPrimeProduct Q y : ℝ)^(-v/B)) =
      primeLaplaceFeature Q B v x := by
  unfold fairSplitAverage
  simp_rw [retainedPrimeProduct_rpow Q]
  rw [show fairRetentionMass x = finiteProductMass (fun p => fairRetentionBitMass (x p)) from rfl,
    finiteProductMass_product_expectation (fun p => fairRetentionBitMass (x p))
      (fun p b => if b then (p.val : ℝ)^(-v/B) else 1)]
  unfold primeLaplaceFeature
  apply prod_congr rfl
  intro p _
  cases x p
  · simp [fairRetentionBitMass]
  · simp [fairRetentionBitMass,bernoulliBitMass]
    ring

theorem primeLaplaceFeature_at_integer (Q : Finset ℕ) (B v : ℝ) {n : ℕ} (hn : n ≠ 0) :
    primeLaplaceFeature Q B v (fun p => decide (p.val ∣ n)) =
      finitePrimeWeight Q (fun p => (1+(p : ℝ)^(-v/B))/2) n := by
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hn,ite_false,primeLaplaceFeature,
    decide_eq_true_eq]
  exact prod_coe_sort Q (fun p => if p ∣ n then (1+(p : ℝ)^(-v/B))/2 else 1)

theorem primeLaplaceWeight_bounds {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime)
    {B v : ℝ} (hB : 0 ≤ B) (hv : 0 ≤ v) (p : ℕ) (hp : p ∈ Q) :
    0 ≤ (1+(p : ℝ)^(-v/B))/2 ∧ (1+(p : ℝ)^(-v/B))/2 ≤ 1 := by
  have hpow : (p : ℝ)^(-v/B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (hQ p hp).one_lt.le)
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv) hB)
  exact ⟨by positivity,by linarith⟩

theorem fairSplitAverage_laplace_sum (Q : Finset ℕ)
    (B : ℝ) (V : Finset ℕ) (a : ℕ → ℝ) (x : Q → Bool) :
    fairSplitAverage x (fun y => ∑ v ∈ V, a v*(retainedPrimeProduct Q y : ℝ)^(-(v : ℝ)/B)) =
      ∑ v ∈ V, a v*primeLaplaceFeature Q B v x := by
  unfold fairSplitAverage
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [← fairSplitAverage_laplace Q B v x]
  unfold fairSplitAverage
  simp only [mul_sum]
  apply sum_congr rfl
  intro y _
  ring

end JointDickman

end OAI
