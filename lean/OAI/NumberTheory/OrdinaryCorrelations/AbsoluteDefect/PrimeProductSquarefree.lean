import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SelbergPrimeSubset
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeLogReciprocalBound

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

namespace OrdinaryWindowEuler
open OrdinarySelbergWeights

lemma prime_product_squarefree (S : Finset ℕ) (hS : ∀p∈S,Nat.Prime p) :
    Squarefree (∏p∈S,p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    apply (hS p hp).coprime_iff_not_dvd.mpr
    intro hd
    exact hpq (((hS q hq).dvd_iff_eq (hS p hp).ne_one).mp hd).symm
  · intro p hp
    exact (hS p hp).squarefree

theorem prime_window_rough (S : Finset ℕ) {Q : ℕ} (hQ : 0<Q)
    (hS : S ⊆ Q.primesLE) (N : ℕ) :
    (((Finset.Icc 1 N).filter (fun n => n.Coprime (∏p∈S,p))).card:ℝ) ≤
      2*(N:ℝ)*Real.exp (-(∑p∈S,(p:ℝ)⁻¹))+(4*(Q:ℝ))^8 := by
  have hprime : ∀p∈S,Nat.Prime p := fun p hp => Nat.prime_of_mem_primesLE (hS hp)
  have hP := prime_product_squarefree S hprime
  have hQp : (0:ℝ)<Q := by exact_mod_cast hQ
  have hz : 1<(4*Q)^2 := by nlinarith
  have hsum : ∑p∈S,Real.log p/p≤Real.log Q+Real.log 4 := by
    apply le_trans _ (OrdinaryPrimeSupply.prime_log_reciprocal_bound Q hQ)
    apply sum_le_sum_of_subset_of_nonneg hS
    intro p hp hnot
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hlog : Real.log (((4*Q)^2:ℕ):ℝ)=2*(Real.log Q+Real.log 4) := by
    push_cast
    rw [Real.log_pow,Real.log_mul (by norm_num) hQp.ne']
    ring
  have hh := window_rough_count (∏p∈S,p) N hP hz
    (by rw [Nat.primeFactors_prod hprime,hlog]; linarith)
  rw [Nat.primeFactors_prod hprime] at hh
  convert hh using 1
  push_cast
  ring

end OrdinaryWindowEuler

end

end OAI
