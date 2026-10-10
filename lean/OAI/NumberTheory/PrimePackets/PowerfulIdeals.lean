import Mathlib
import OAI.NumberTheory.PrimePackets.DivisorBounds

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
namespace PrimeDegreePackets
open Finset Nat

lemma isPowerful_mul_iff {a b : ℕ} (hab : a.Coprime b) :
    IsPowerful (a*b) ↔ IsPowerful a ∧ IsPowerful b := by
  by_cases ha : a=0
  · simp [ha, IsPowerful]
  by_cases hb : b=0
  · simp [hb, IsPowerful]
  have heqa : ∀ p ∈ a.primeFactors, (a*b).factorization p = a.factorization p := by
    intro p hp
    apply Nat.factorization_eq_of_coprime_left hab
    exact (Nat.mem_primeFactorsList_iff_dvd ha (Nat.prime_of_mem_primeFactors hp)).mpr (Nat.dvd_of_mem_primeFactors hp)
  have heqb : ∀ p ∈ b.primeFactors, (a*b).factorization p = b.factorization p := by
    intro p hp
    apply Nat.factorization_eq_of_coprime_right hab
    exact (Nat.mem_primeFactorsList_iff_dvd hb (Nat.prime_of_mem_primeFactors hp)).mpr (Nat.dvd_of_mem_primeFactors hp)
  constructor
  · intro hm
    constructor
    · refine ⟨ha, ?_⟩
      intro p hp
      rw [← heqa p hp]
      exact hm.2 p (by rw [Nat.primeFactors_mul ha hb]; exact Finset.mem_union_left _ hp)
    · refine ⟨hb, ?_⟩
      intro p hp
      rw [← heqb p hp]
      exact hm.2 p (by rw [Nat.primeFactors_mul ha hb]; exact Finset.mem_union_right _ hp)
  · rintro ⟨hpa,hpb⟩
    refine ⟨mul_ne_zero ha hb, ?_⟩
    intro p hp
    rw [Nat.primeFactors_mul ha hb, Finset.mem_union] at hp
    rcases hp with hp | hp
    · rw [heqa p hp]
      exact hpa.2 p hp
    · rw [heqb p hp]
      exact hpb.2 p hp

lemma isPowerful_prime_pow {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) : IsPowerful (p^j) := by
  refine ⟨pow_ne_zero _ hp.ne_zero, ?_⟩
  intro q hq
  rw [Nat.primeFactors_pow _ (by omega : j ≠ 0), hp.primeFactors, Finset.mem_singleton] at hq
  subst q
  simpa [Nat.factorization_pow, hp.factorization] using hj

lemma powerfulCorrection_one (k : ℕ) : powerfulCorrection k 1 = 1 := by
  have hn : nFoldDivisor (k+1) 1 = 1 := ArithmeticFunction.IsMultiplicative.map_one (ArithmeticFunction.isMultiplicative_zeta.pow)
  simp [powerfulCorrection, IsPowerful, hn]

 
def powerfulFunction (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨powerfulCorrection k, powerfulCorrection_zero k⟩

lemma powerfulFunction_apply (k m : ℕ) : powerfulFunction k m = powerfulCorrection k m := rfl

lemma powerfulFunction_multiplicative (k : ℕ) : (powerfulFunction k).IsMultiplicative := by
  classical
  refine ⟨powerfulCorrection_one k, ?_⟩
  intro a b hab
  simp only [powerfulFunction_apply, powerfulCorrection, isPowerful_mul_iff hab]
  have hn : nFoldDivisor (k+1) (a*b) = nFoldDivisor (k+1) a * nFoldDivisor (k+1) b :=
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (ArithmeticFunction.isMultiplicative_zeta.pow) hab
  split_ifs <;> simp_all

end PrimeDegreePackets

open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
namespace PrimeDegreePackets.Sieve

 
lemma sum_moebius_div_indicator (l k : ℕ) (hk : 0 < k) :
    (∑ d ∈ k.divisors, if l ∣ d then (μ (k / d) : ℝ) else 0) =
      if k = l then 1 else 0 := by
  have H : ∀ n > 0, (∑ i ∈ n.divisors, if i = l then (1 : ℝ) else 0) =
      if l ∣ n then 1 else 0 := by
    intro n hn
    simp [Nat.mem_divisors, hn.ne']
  have H' := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp H) k hk
  rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => (μ x : ℝ) * (if l ∣ y then 1 else 0))] at H'
  simpa only [mul_ite, mul_one, mul_zero] using H'

lemma sum_moebius_interval {P l k : ℕ} (hP : P ≠ 0) (hk : k ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ k then (μ (k / d) : ℝ) else 0) =
      if k = l then 1 else 0 := by
  have H := sum_moebius_div_indicator l k (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hk))
  rw [← Nat.divisors_filter_dvd_of_dvd hP hk, Finset.sum_filter] at H
  simpa only [← ite_and, and_comm] using H

 
def multipleMobius (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ P.divisors, if d ∣ k then (μ (k / d) : ℝ) * y k else 0

lemma sum_multipleMobius {P l : ℕ} (hP : P ≠ 0) (hl : l ∣ P) (y : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then multipleMobius P y d else 0) = y l := by
  simp only [multipleMobius, Finset.ite_sum_zero, ← ite_and]
  rw [Finset.sum_comm]
  calc
    (∑ k ∈ P.divisors, ∑ d ∈ P.divisors,
      if l ∣ d ∧ d ∣ k then (μ (k / d) : ℝ) * y k else 0) =
        ∑ k ∈ P.divisors,
          (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ k then (μ (k / d) : ℝ) else 0) * y k := by
      simp only [Finset.sum_mul, ite_mul, zero_mul]
    _ = ∑ k ∈ P.divisors, (if k = l then (1 : ℝ) else 0) * y k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [sum_moebius_interval hP (Nat.dvd_of_mem_divisors hk)]
    _ = y l := by
      simp [ite_mul, Nat.mem_divisors.mpr ⟨hl, hP⟩]

 
def sieveDenominator (s : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ k ∈ s.prodPrimes.divisors, if k ≤ z then s.selbergTerms k else 0

def optimalY (s : BoundingSieve) (z : ℕ) (k : ℕ) : ℝ :=
  if k ≤ z then (μ k : ℝ) * s.selbergTerms k / sieveDenominator s z else 0

def optimalWeight (s : BoundingSieve) (z : ℕ) (d : ℕ) : ℝ :=
  (s.nu d)⁻¹ * multipleMobius s.prodPrimes (optimalY s z) d

lemma sieveDenominator_pos (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    0 < sieveDenominator s z := by
  unfold sieveDenominator
  apply Finset.sum_pos'
  · intro k hk
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hk)).le
    · rfl
  · refine ⟨1, Nat.one_mem_divisors.mpr s.prodPrimes_ne_zero, ?_⟩
    rw [ite_eq_left hz]
    exact s.selbergTerms_pos (one_dvd _)

lemma nu_mul_optimalWeight (s : BoundingSieve) (z : ℕ) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    s.nu d * optimalWeight s z d = multipleMobius s.prodPrimes (optimalY s z) d := by
  rw [optimalWeight, ← mul_assoc, mul_inv_cancel₀ (s.nu_ne_zero hd), one_mul]

lemma optimalWeight_transform (s : BoundingSieve) (z : ℕ) {l : ℕ} (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * optimalWeight s z d else 0) =
      optimalY s z l := by
  convert sum_multipleMobius s.prodPrimes_ne_zero hl (optimalY s z) using 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [nu_mul_optimalWeight s z (Nat.dvd_of_mem_divisors hd)]

lemma optimalWeight_one (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    optimalWeight s z 1 = 1 := by
  have hD : sieveDenominator s z ≠ 0 := (sieveDenominator_pos s hz).ne'
  unfold optimalWeight multipleMobius
  rw [s.nu_mult.map_one, inv_one, one_mul]
  simp only [one_dvd, ite_true, Nat.div_one, optimalY, mul_ite, mul_zero]
  have H : ∀ k ∈ s.prodPrimes.divisors,
      (μ k : ℝ) * ((μ k : ℝ) * s.selbergTerms k / sieveDenominator s z) =
      s.selbergTerms k / sieveDenominator s z := by
    intro k hk
    have hm : (μ k : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (s.squarefree_of_mem_divisors_prodPrimes hk)
    calc
      _ = (μ k : ℝ)^2 * s.selbergTerms k / sieveDenominator s z := by ring
      _ = _ := by rw [hm, one_mul]
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun a => if k ≤ z then a else 0) (H k hk))]
  rw [show (∑ k ∈ s.prodPrimes.divisors, if k ≤ z then s.selbergTerms k / sieveDenominator s z else 0) =
      sieveDenominator s z / sieveDenominator s z by
    simp only [sieveDenominator, Finset.sum_div, ite_div, zero_div]]
  exact div_self hD

lemma optimalWeight_mainSum (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (optimalWeight s z)) =
      (sieveDenominator s z)⁻¹ := by
  have hD : sieveDenominator s z ≠ 0 := (sieveDenominator_pos s hz).ne'
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc
    (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * optimalWeight s z d else 0) ^ 2) =
      ∑ l ∈ s.prodPrimes.divisors,
        (if l ≤ z then s.selbergTerms l else 0) / (sieveDenominator s z)^2 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [optimalWeight_transform s z (Nat.dvd_of_mem_divisors hl)]
      unfold optimalY
      split_ifs with h
      · have hg : s.selbergTerms l ≠ 0 := (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).ne'
        have hm : (μ l : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
            (s.squarefree_of_mem_divisors_prodPrimes hl)
        rw [div_pow, mul_pow, hm, one_mul]
        field_simp
      · simp
    _ = sieveDenominator s z / (sieveDenominator s z)^2 := by rw [← Finset.sum_div]; rfl
    _ = (sieveDenominator s z)⁻¹ := by field_simp

lemma optimalWeight_eq_zero_of_lt (s : BoundingSieve) {z d : ℕ} (h : z < d) :
    optimalWeight s z d = 0 := by
  unfold optimalWeight multipleMobius
  suffices (∑ k ∈ s.prodPrimes.divisors,
      if d ∣ k then (μ (k / d) : ℝ) * optimalY s z k else 0) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hd : d ∣ k
  · have hdk := Nat.le_of_dvd (Nat.pos_of_mem_divisors hk) hd
    simp [hd, optimalY, show ¬ k ≤ z by omega]
  · simp [hd]

lemma abs_optimalWeight_le (s : BoundingSieve) {z d : ℕ} (hz : 1 ≤ z)
    (hd : d ∣ s.prodPrimes) : |optimalWeight s z d| ≤ (s.nu d)⁻¹ := by
  have hD := sieveDenominator_pos s hz
  have hnu := s.nu_pos_of_dvd_prodPrimes hd
  have hm (k : ℕ) : |(μ k : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
  have hy (k : ℕ) (hk : k ∈ s.prodPrimes.divisors) :
      |optimalY s z k| ≤ (if k ≤ z then s.selbergTerms k else 0) / sieveDenominator s z := by
    unfold optimalY
    split_ifs with h
    · rw [abs_div, abs_mul, abs_of_pos (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hk)),
        abs_of_pos hD]
      exact div_le_div_of_nonneg_right (by nlinarith [s.selbergTerms_pos (Nat.dvd_of_mem_divisors hk), hm k]) hD.le
    · simp
  unfold optimalWeight multipleMobius
  rw [abs_mul, abs_inv, abs_of_pos hnu]
  apply mul_le_of_le_one_right (inv_nonneg.mpr hnu.le)
  calc
    |∑ k ∈ s.prodPrimes.divisors,
      if d ∣ k then (μ (k / d) : ℝ) * optimalY s z k else 0| ≤
        ∑ k ∈ s.prodPrimes.divisors,
          (if k ≤ z then s.selbergTerms k else 0) / sieveDenominator s z := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk' : d ∣ k
      · rw [ite_eq_left hk', abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hm _)).trans (hy k hk)
      · rw [ite_eq_right hk', abs_zero]
        exact (abs_nonneg _).trans (hy k hk)
    _ = 1 := by
      rw [← Finset.sum_div]
      exact div_self hD.ne'

lemma sum_divisors_lambdaSquared (P : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d) =
      (∑ d ∈ P.divisors, w d)^2 := by
  have he (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ d ∈ P.divisors, ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
        if d = Nat.lcm d₁ d₂ then f d₁ d₂ d else 0) =
      (∑ d ∈ P.divisors, ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
        if d = Nat.lcm d₁ d₂ then f d₁ d₂ d else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hdP, hP⟩ := Nat.mem_divisors.mp hd
    have H : ∀ d₁ d₂, (d₁ ∣ d ∧ d₂ ∣ d ∧ d = d₁.lcm d₂) = (d = d₁.lcm d₂) := by
      intro d₁ d₂
      simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hP hdP, Finset.sum_filter,
      Finset.ite_sum_zero, ← ite_and, H]
  unfold BoundingSieve.lambdaSquared
  rw [he, Finset.sum_comm, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d₁ h₁
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d₂ h₂
  apply Finset.sum_ite_eq_of_mem'
  exact Nat.mem_divisors.mpr ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors h₁)
    (Nat.dvd_of_mem_divisors h₂), (Nat.mem_divisors.mp h₁).2⟩

lemma abs_lambdaSquared_le (w : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared w d| ≤ BoundingSieve.lambdaSquared (fun k => |w k|) d := by
  unfold BoundingSieve.lambdaSquared
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d₁ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d₂ _
  split_ifs <;> simp [abs_mul]

lemma errSum_lambdaSquared_le (s : BoundingSieve) (w : ℕ → ℝ) {R : ℝ}
    (_hR : 0 ≤ R) (hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ R) :
    s.errSum (BoundingSieve.lambdaSquared w) ≤
      R * (∑ d ∈ s.prodPrimes.divisors, |w d|)^2 := by
  unfold BoundingSieve.errSum
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        BoundingSieve.lambdaSquared (fun k => |w k|) d * R := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul (abs_lambdaSquared_le w d) (hrem d hd) (abs_nonneg _)
        ((abs_nonneg _).trans (abs_lambdaSquared_le w d))
    _ = _ := by rw [← Finset.sum_mul, sum_divisors_lambdaSquared, mul_comm]

lemma optimalWeight_errSum_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) {R : ℝ}
    (hR : 0 ≤ R) (hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ R) :
    s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) ≤
      R * (∑ d ∈ s.prodPrimes.divisors, if d ≤ z then (s.nu d)⁻¹ else 0)^2 := by
  apply (errSum_lambdaSquared_le s _ hR hrem).trans
  apply mul_le_mul_of_nonneg_left _ hR
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  apply Finset.sum_le_sum
  intro d hd
  split_ifs with h
  · exact abs_optimalWeight_le s hz (Nat.dvd_of_mem_divisors hd)
  · rw [optimalWeight_eq_zero_of_lt s (by omega), abs_zero]

 

theorem optimized_sieve_bound (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / sieveDenominator s z +
      s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) := by
  have H := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared (optimalWeight s z))
    (BoundingSieve.upperMoebius_lambdaSquared _ (optimalWeight_one s hz))
  rw [optimalWeight_mainSum s hz] at H
  simpa only [div_eq_mul_inv] using H

end PrimeDegreePackets.Sieve

open scoped BigOperators Classical
open Finset Nat
namespace PrimeDegreePackets.Sieve

def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma radical_dvd (n : ℕ) : radical n ∣ n := Nat.prod_primeFactors_dvd n

lemma radical_pos (n : ℕ) : 0 < radical n :=
  Finset.prod_pos (fun _p hp => Nat.pos_of_mem_primeFactors hp)

lemma primeFactors_radical (n : ℕ) : (radical n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod_primeFactors n

lemma div_radical_factored {n : ℕ} (hn : n ≠ 0) :
    n / radical n ∈ Nat.factoredNumbers (radical n).primeFactors := by
  refine ⟨Nat.div_ne_zero_iff.mpr ⟨(radical_pos n).ne', Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (radical_dvd n)⟩, ?_⟩
  intro p hp
  rw [primeFactors_radical]
  apply Nat.primeFactors_mono (Nat.div_dvd_of_dvd (radical_dvd n)) hn
  exact Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp

lemma reciprocal_factored_hasSum (d : ℕ) :
    HasSum (fun m : Nat.factoredNumbers d.primeFactors => (m.val : ℝ)⁻¹)
      (∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) := by
  have hsum {p : ℕ} (hp : p.Prime) :
      Summable (fun j : ℕ => ‖((p ^ j : ℕ) : ℝ)⁻¹‖) := by
    have hp2 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    simpa only [Nat.cast_pow, Real.norm_eq_abs, abs_pow, abs_inv,
      abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p), inv_pow] using
      (summable_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p))
        (inv_lt_one_of_one_lt₀ hp2))
  have H := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (n : ℝ)⁻¹) (by simp)
    (fun {m n} _ => by simp [Nat.cast_mul, mul_inv_rev, mul_comm])
    (fun {p} hp => hsum hp) d.primeFactors
  have he : (∏ p ∈ d.primeFactors with p.Prime, ∑' j : ℕ, ((p ^ j : ℕ) : ℝ)⁻¹) =
      ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [Finset.filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    simpa only [Nat.cast_pow, inv_pow] using tsum_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p))
      (inv_lt_one_of_one_lt₀ hp2)
  exact he ▸ H.2

lemma reciprocal_radical_class_bound (A : Finset ℕ) {d : ℕ}
    (hA : ∀ n ∈ A, n ≠ 0 ∧ radical n = d) :
    (∑ n ∈ A, (n : ℝ)⁻¹) ≤ (d.totient : ℝ)⁻¹ := by
  let e : A → Nat.factoredNumbers d.primeFactors := fun n =>
    ⟨n.val / d, by rw [← (hA n.val n.property).2]; exact div_radical_factored (hA n.val n.property).1⟩
  have hmul (n : A) : d * (n.val / d) = n.val := by
    rw [← (hA n.val n.property).2]
    exact Nat.mul_div_cancel' (radical_dvd n.val)
  have he : Function.Injective e := by
    intro m n h
    apply Subtype.ext
    have H := congrArg (fun x : Nat.factoredNumbers d.primeFactors => d * x.val) h
    exact (hmul m).symm.trans (H.trans (hmul n))
  have hsum := (reciprocal_factored_hasSum d).mul_left ((d : ℝ)⁻¹)
  have H := Summable.tsum_le_tsum_of_inj e he
    (fun _ _ => by positivity)
    (f := fun n : A => (n.val : ℝ)⁻¹)
    (g := fun m : Nat.factoredNumbers d.primeFactors => (d : ℝ)⁻¹ * (m.val : ℝ)⁻¹)
    (fun n => le_of_eq (by
      change (n.val : ℝ)⁻¹ = (d : ℝ)⁻¹ * ((n.val / d : ℕ) : ℝ)⁻¹
      rw [← mul_inv_rev, ← Nat.cast_mul, Nat.mul_comm, hmul n]))
    Summable.of_finite hsum.summable
  rw [tsum_fintype, Finset.sum_coe_sort A (fun n => (n : ℝ)⁻¹), hsum.tsum_eq] at H
  have ht : (d.totient : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have H := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors d)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using H
  simpa only [ht, mul_inv_rev, Finset.prod_inv_distrib, mul_comm] using H

 

theorem harmonic_le_inverse_totient_sum {P z : ℕ} (hP : P ≠ 0)
    (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ P) :
    (harmonic z : ℝ) ≤ ∑ d ∈ P.divisors, if d ≤ z then (d.totient : ℝ)⁻¹ else 0 := by
  let A := Finset.Icc 1 z
  let D := P.divisors.filter (fun d => d ≤ z)
  have hmap : ∀ n ∈ A, radical n ∈ D := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    apply Finset.mem_filter.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      refine ⟨Nat.prod_primeFactors_dvd_iff hP |>.mpr ?_, hP⟩
      intro p hp
      exact (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
        hprimes p (Nat.prime_of_mem_primeFactors hp)
          ((Nat.le_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)).trans (Finset.mem_Icc.mp hn).2), hP⟩)
    · exact (Nat.le_of_dvd hn0 (radical_dvd n)).trans (Finset.mem_Icc.mp hn).2
  have he : (∑ n ∈ A, (n : ℝ)⁻¹) =
      ∑ d ∈ D, ∑ n ∈ A with radical n = d, (n : ℝ)⁻¹ := by
    exact (Finset.sum_fiberwise_of_maps_to hmap (fun n => (n : ℝ)⁻¹)).symm
  calc
    (harmonic z : ℝ) = ∑ n ∈ A, (n : ℝ)⁻¹ := by
      simp only [A, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ = _ := he
    _ ≤ ∑ d ∈ D, (d.totient : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d _
      exact reciprocal_radical_class_bound _ (fun n hn =>
        ⟨by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1; omega,
          (Finset.mem_filter.mp hn).2⟩)
    _ = _ := Finset.sum_filter _ _

end PrimeDegreePackets.Sieve
end
end

end OAI
