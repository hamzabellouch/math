import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualArrayMeanScales
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsGrid
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyEnvelopeEnergy
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencySupport
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessStatistics

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem primeProduct_phase_bounds {q : ℕ} (hq : Squarefree q) (t : ℕ → ℤ) :
    0 ≤ (primeProductCenter q t:ℝ)/q ∧ (primeProductCenter q t:ℝ)/q ≤ 1 := by
  have hqp : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq.ne_zero
  refine ⟨by positivity,?_⟩
  have hc := primeBlockCenter_lt q.primeFactors (fun p hp => (Nat.mem_primeFactors.mp hp).1) t
  rw [Nat.prod_primeFactors_of_squarefree hq] at hc
  exact (div_le_one hqp).mpr (by exact_mod_cast hc.le)

theorem witness_radius_usable {L Z : ℕ} (hZ : 1 ≤ Z) (hLZ : L ≤ Z) {R : ℝ}
    (hRlo : (Z:ℝ)^10 ≤ R) (hRhi : R ≤ (Z:ℝ)^13) :
    1 ≤ R ∧ R ≤ (2*Z^13:ℕ) ∧ (L^6:ℕ) ≤ R := by
  have hZr : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  refine ⟨(one_le_pow₀ hZr).trans hRlo,?_,?_⟩
  · push_cast
    exact hRhi.trans (by have := pow_nonneg (Nat.cast_nonneg Z : (0:ℝ) ≤ _) 13; linarith)
  · exact adaptive_small_radius_lower hZ hLZ (by simpa only [Nat.cast_pow] using hRlo)

theorem primeProductLargeSum_le_family {L Z q : ℕ} [NeZero L]
    (hL : Squarefree L) (hZ : 1 ≤ Z) (hLZ : L ≤ Z)
    (hC : adaptiveArrayConstant ≤ (Z:ℝ)) (hq : Squarefree q) (ho : Odd q)
    (A : ∀p:ℕ,Finset (ZMod p)) (X : ℝ) (t : ℕ → ℤ)
    (hRlo : (Z:ℝ)^10 ≤ (q:ℝ)/X) (hRhi : (q:ℝ)/X ≤ (Z:ℝ)^13) :
    ‖primeProductLargeSum L Z A (1/16) X t q‖ ≤
      witnessFamilyMax (witnessLargeFamily L Z A)
        (adaptiveArraySupport L Z \ adaptiveSmallSupport L) q+(Z:ℝ)^(-(66:ℝ)) := by
  classical
  have hR := witness_radius_usable hZ hLZ hRlo hRhi
  have ht := primeProduct_phase_bounds hq t
  obtain ⟨a,ha,hPa,hnear⟩ := exists_near_witnessGridArray hL hZ hLZ hC ho (le_refl 1)
    (Nat.one_le_pow 7 Z hZ) A (centerCorrection q L (primeProductCenter q t)) ht.1 ht.2 hR.1 hR.2.1
  have hb : witnessGridArray L Z A a ∈ witnessLargeFamily L Z A :=
    Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hPa⟩,rfl⟩
  apply witness_sum_le_near_family _ q (primeProductArrayCoefficient L A (1/16) X t q 1) hb
  apply (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun s _ _ => norm_nonneg _)).trans
  apply adaptiveArray_total_error hZ
  intro s hs
  simpa only [primeProductArrayCoefficient,Int.cast_natCast] using hnear s hs

theorem primeProductSmallSum_le_family {L Z q : ℕ} [NeZero L]
    (hL : Squarefree L) (hZ : 1 ≤ Z) (hLZ : L ≤ Z)
    (hC : adaptiveArrayConstant ≤ (Z:ℝ)) (hq : Squarefree q) (ho : Odd q)
    (A : ∀p:ℕ,Finset (ZMod p)) (X : ℝ) (t : ℕ → ℤ)
    (hRlo : (Z:ℝ)^10 ≤ (q:ℝ)/X) (hRhi : (q:ℝ)/X ≤ (Z:ℝ)^13) :
    ‖primeProductSmallSum L A (1/16) X t q‖ ≤
      witnessFamilyMax (adaptiveSmallArrayFamily L Z (1/16) A)
        (adaptiveSmallSupport L) q+(Z:ℝ)^(-(66:ℝ)) := by
  have hR := witness_radius_usable hZ hLZ hRlo hRhi
  have ht := primeProduct_phase_bounds hq t
  obtain ⟨a,ha,hb,hnear⟩ := exists_near_adaptiveSmallArrayFamily hL hZ hLZ hC ho
    (by norm_num : |(1/16:ℝ)| ≤ 1) A (centerCorrection q L (primeProductCenter q t))
    ht.1 ht.2 hR.2.2 hR.2.1
  rw [primeProductSmallSum_eq_actualSmallArray]
  exact witness_sum_le_near_family _ q _ hb (adaptiveSmallArray_total_error hZ hLZ _ _ hnear)

theorem primeProductSmallOffEventNorm_le_family {L Z q : ℕ} [NeZero L]
    (hL : Squarefree L) (hZ : 1 ≤ Z) (hLZ : L ≤ Z)
    (hC : adaptiveArrayConstant ≤ (Z:ℝ)) (hq : Squarefree q) (ho : Odd q)
    (A : ∀p:ℕ,Finset (ZMod p)) (X K : ℝ) (t : ℕ → ℤ)
    (hRlo : (Z:ℝ)^10 ≤ (q:ℝ)/X) (hRhi : (q:ℝ)/X ≤ (Z:ℝ)^13)
    (hK : 10 ≤ K) (hKZ : K ≤ Real.log Z) :
    primeProductSmallOffEventNorm L A (1/16) X K t q ≤
      witnessFamilyMax (adaptiveOffEventArrayFamily L Z (1/16) A K)
        (adaptiveSmallSupport L) q+(Z:ℝ)^(-(66:ℝ)) := by
  classical
  unfold primeProductSmallOffEventNorm
  split_ifs with he
  · exact add_nonneg (witnessFamilyMax_nonneg _ _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · have hR := witness_radius_usable hZ hLZ hRlo hRhi
    have ht := primeProduct_phase_bounds hq t
    have hno := not_smallQuadraticWitness_imp_noSmallWitness he
    obtain ⟨a,ha,hb,hnear⟩ := exists_near_adaptiveOffEventArrayFamily hL hZ hLZ hC ho
      (by norm_num : |(1/16:ℝ)| ≤ 1) A (centerCorrection q L (primeProductCenter q t))
      ht.1 ht.2 hR.2.2 hR.2.1 hK hKZ hno
    rw [primeProductSmallSum_eq_actualSmallArray]
    exact witness_sum_le_near_family _ q _ hb (adaptiveSmallArray_total_error hZ hLZ _ _ hnear)

theorem primeProductSamples_primeFactors_subset {P : Finset ℕ} (hP : ∀p∈P,p.Prime)
    {k q : ℕ} (hq : q ∈ primeProductSamples P k) : q.primeFactors ⊆ P := by
  obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hq
  exact primeSubsetProduct_primeFactors_subset hP U

theorem squarefree_divisors_card_real {q : ℕ} (hq : Squarefree q) :
    (q.divisors.card:ℝ)=(2:ℝ)^q.primeFactors.card := by
  simpa only [one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,show (1:ℝ)+1=2 by norm_num] using positive_array_divisor_weight_sum hq 1

theorem primeProductNontrivialSum_le_family {L Z q : ℕ} [NeZero L]
    (hL : Squarefree L) (hZ : 1 ≤ Z) (hLZ : L ≤ Z)
    (hC : adaptiveArrayConstant ≤ (Z:ℝ)) (hq : Squarefree q) (ho : Odd q)
    (hprimes : ∀p∈q.primeFactors,Z ≤ p)
    (A : ∀p:ℕ,Finset (ZMod p)) (X : ℝ) (t : ℕ → ℤ)
    (hRlo : (Z:ℝ)^10 ≤ (q:ℝ)/X) (hRhi : (q:ℝ)/X ≤ (Z:ℝ)^13) :
    ‖primeProductNontrivialSum L Z A (1/16) X t q‖ ≤
      (2:ℝ)^q.primeFactors.card * (witnessFamilyMax (witnessNontrivialFamily L Z A)
        (adaptiveArraySupport L Z) q+(Z:ℝ)^(-(66:ℝ))) := by
  classical
  have hR := witness_radius_usable hZ hLZ hRlo hRhi
  have ht := primeProduct_phase_bounds hq t
  have hRpos : 0 < (q:ℝ)/X := by linarith [hR.1]
  have hcut : ((q:ℝ)/X)*(L:ℝ) ≤ (Z^7:ℝ)^2 := by
    calc
      _ ≤ (Z:ℝ)^13*(Z:ℝ) := mul_le_mul hRhi (by exact_mod_cast hLZ) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  let D := witnessFamilyMax (witnessNontrivialFamily L Z A) (adaptiveArraySupport L Z) q+(Z:ℝ)^(-(66:ℝ))
  have hD : 0 ≤ D := add_nonneg (witnessFamilyMax_nonneg _ _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hterm : ∀P∈q.divisors.erase 1,
      ‖(-1:ℂ)^P.primeFactors.card * ∑s∈adaptiveArraySupport L Z,
        primeProductArrayCoefficient L A (1/16) X t q P s*(jacobiSym (s:ℤ) q:ℂ)‖ ≤ D := by
    intro P hP
    obtain ⟨hPone,hPd⟩ := Finset.mem_erase.mp hP
    have hPpos := Nat.pos_of_mem_divisors hPd
    have hPZ := nontrivial_divisor_ge_prime_lower hq.ne_zero (Nat.dvd_of_mem_divisors hPd) hPone hprimes
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    by_cases hPW : P ≤ Z^7
    · obtain ⟨a,ha,hPa,hnear⟩ := exists_near_witnessGridArray hL hZ hLZ hC ho hPpos hPW A
        (centerCorrection q L (primeProductCenter q t)) ht.1 ht.2 hR.1 hR.2.1
      have hb : witnessGridArray L Z A a ∈ witnessNontrivialFamily L Z A :=
        Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,by simpa only [hPa] using hPZ⟩,rfl⟩
      exact witness_sum_le_near_family _ q _ hb (adaptiveArray_total_error hZ _ _
        (fun s hs => by simpa only [primeProductArrayCoefficient,Int.cast_natCast] using hnear s hs))
    · have hs0 : ∑s∈adaptiveArraySupport L Z,
          primeProductArrayCoefficient L A (1/16) X t q P s*(jacobiSym (s:ℤ) q:ℂ)=0 := by
        apply Finset.sum_eq_zero
        intro s hs
        have hspos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
        have he := positiveDivisorArray_eq_zero_of_large_P hL q (1/16) A (adaptiveInverse q)
          hspos hRpos (centerCorrection q L (primeProductCenter q t)) ((primeProductCenter q t:ℝ)/q)
          (B:=Z^7) (P:=P) (by simpa only [Nat.cast_pow] using hcut) (by omega)
        simp only [primeProductArrayCoefficient,he,zero_mul]
      rw [hs0,norm_zero]
      exact hD
  calc
    _ ≤ ∑P∈q.divisors.erase 1,‖(-1:ℂ)^P.primeFactors.card * ∑s∈adaptiveArraySupport L Z,
        primeProductArrayCoefficient L A (1/16) X t q P s*(jacobiSym (s:ℤ) q:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑_P∈q.divisors.erase 1,D := Finset.sum_le_sum hterm
    _ = ((q.divisors.erase 1).card:ℝ)*D := by simp
    _ ≤ (q.divisors.card:ℝ)*D := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hD
    _ = _ := by rw [squarefree_divisors_card_real hq]

end Ostmann.QuadraticCenter

end

end OAI
