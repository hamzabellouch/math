import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NatDivRealError
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PowersetFirstMoment

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

lemma selberg_prime_subset (P : ℕ) (hP : Squarefree P) (A : Finset ℕ)
    (hA : ∀p∈A,Nat.Prime p) :
    (reciprocalSieve P hP).selbergTerms (∏p∈A,p)=∏p∈A,primeWeight p := by
  rw [BoundingSieve.selbergTerms_apply,Nat.primeFactors_prod hA]
  change ((∏p∈A,p:ℕ):ℝ)⁻¹*(∏p∈A,(1-(p:ℝ)⁻¹)⁻¹)=_
  rw [Nat.cast_prod,←Finset.prod_inv_distrib,←Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have hp1 : (1:ℝ)<p := by exact_mod_cast (hA p hp).one_lt
  have hp0 : (p:ℝ)≠0 := by linarith
  have hn : (p:ℝ)-1≠0 := by linarith
  unfold primeWeight
  field_simp [hp0,hn]

lemma powerset_mass (P z : ℕ) (hP : Squarefree P) :
    (∑A∈P.primeFactors.powerset,
      if (∏p∈A,p)≤z then ∏p∈A,primeWeight p else 0)=actualMass P z hP := by
  unfold actualMass mass
  change _ = ∑d∈P.divisors,if d≤z then (reciprocalSieve P hP).selbergTerms d else 0
  apply sum_bij (fun A _ => ∏p∈A,p)
  · intro A hA
    apply Nat.mem_divisors.mpr
    constructor
    · rw [←Nat.prod_primeFactors_of_squarefree hP]
      exact prod_dvd_prod_of_subset A P.primeFactors id (mem_powerset.mp hA)
    · exact hP.ne_zero
  · intro A hA B hB he
    have ha : ∀p∈A,Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hA hp)
    have hb : ∀p∈B,Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hB hp)
    simpa only [Nat.primeFactors_prod ha,Nat.primeFactors_prod hb] using congrArg Nat.primeFactors he
  · intro d hd
    refine ⟨d.primeFactors,?_,?_⟩
    · exact mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hP.ne_zero)
    · exact Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
  · intro A hA
    rw [selberg_prime_subset P hP A (fun p hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hA hp))]

theorem actualMass_window (P : ℕ) (hP : Squarefree P) {z : ℕ} (hz : 1<z)
    (hm : 2*(∑p∈P.primeFactors,Real.log p/p)≤Real.log z) :
    Real.exp (∑p∈P.primeFactors,(p:ℝ)⁻¹)/2≤actualMass P z hP := by
  have hS : ∀p∈P.primeFactors,Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hh := truncated_prime_mass P.primeFactors hS hz hm
  rw [powerset_mass P z hP] at hh
  exact (div_le_div_of_nonneg_right (prime_log_mass P.primeFactors hS) (by norm_num)).trans hh

theorem window_rough_count (P N : ℕ) (hP : Squarefree P) {z : ℕ} (hz : 1<z)
    (hm : 2*(∑p∈P.primeFactors,Real.log p/p)≤Real.log z) :
    (((Finset.Icc 1 N).filter (fun n => n.Coprime P)).card:ℝ) ≤
      2*(N:ℝ)*Real.exp (-(∑p∈P.primeFactors,(p:ℝ)⁻¹))+(z:ℝ)^4 := by
  have hb := rough_count_bound P z N hP hz.le
  have hm' := actualMass_window P hP hz hm
  have he : 0<Real.exp (∑p∈P.primeFactors,(p:ℝ)⁻¹)/2 := by positivity
  have hi := inv_anti₀ he hm'
  have hi' : (actualMass P z hP)⁻¹≤2*Real.exp (-(∑p∈P.primeFactors,(p:ℝ)⁻¹)) := by
    simpa only [Real.exp_neg,div_eq_mul_inv,mul_inv_rev,inv_inv] using hi
  calc
    _ ≤ _ := hb
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hi' (Nat.cast_nonneg N : (0:ℝ)≤N)]

end OrdinaryWindowEuler

end

end OAI
