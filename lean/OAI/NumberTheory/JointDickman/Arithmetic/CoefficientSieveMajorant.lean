import OAI.NumberTheory.JointDickman.Arithmetic.SieveScale
import OAI.NumberTheory.JointDickman.Arithmetic.ThreeFormSieve
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeHarmonicWeights

namespace OAI

/-! # Truncating the prime conditions majorizes the actual coefficients -/

namespace JointDickman

open Finset

noncomputable def sievedCoefficientWeight (P Z n : ℕ) : ℝ :=
  ∏ p ∈ sievePrimes Z, residueWeight (roughSieveTheta P p) 0 (n : ZMod p)

theorem sievedCoefficientWeight_nonneg (P Z n : ℕ) : 0 ≤ sievedCoefficientWeight P Z n :=
  prod_nonneg (fun p _ => residueWeight_nonneg _ _ (roughSieveTheta_bounds P p).1)

theorem roughSquarefreeWeight_le_sieved (P Z n : ℕ) :
    roughSquarefreeWeight (Nat.primesLE P) (1 / 2) n ≤ sievedCoefficientWeight P Z n := by
  classical
  by_cases hd : Disjoint n.primeFactors (Nat.primesLE P)
  · by_cases hsq : Squarefree n
    · have hcard : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
        calc
          _ = ArithmeticFunction.cardFactors (∏ p ∈ n.primeFactors, p) :=
            congrArg ArithmeticFunction.cardFactors (Nat.prod_primeFactors_of_squarefree hsq).symm
          _ = _ := primeProduct_cardFactors _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
      have heq (p : ℕ) (hp : p ∈ sievePrimes Z) :
          residueWeight (roughSieveTheta P p) 0 (n : ZMod p) =
            if p ∣ n then (1 / 2 : ℝ) else 1 := by
        have hpprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
        by_cases hpn : p ∣ n
        · have hpP : ¬ p ≤ P := by
            intro h
            exact disjoint_left.mp hd (hpprime.mem_primeFactors hpn hsq.ne_zero)
              (Nat.mem_primesLE.mpr ⟨h, hpprime⟩)
          simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn, roughSieveTheta, hpP]
        · simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn]
      have hsub : (sievePrimes Z).filter (fun p => p ∣ n) ⊆ n.primeFactors := by
        intro p hp
        have hmem := mem_filter.mp hp
        exact (Nat.mem_primesLE.mp (mem_filter.mp hmem.1).1).2.mem_primeFactors hmem.2 hsq.ne_zero
      have hsieve : sievedCoefficientWeight P Z n =
          (1 / 2 : ℝ) ^ ((sievePrimes Z).filter (fun p => p ∣ n)).card := by
        unfold sievedCoefficientWeight
        simp_rw [prod_congr rfl heq, ← prod_filter]
        simp
      rw [roughSquarefreeWeight, ArithmeticFunction.coe_mk, ite_eq_left hd,
        squarefreeWeight, ArithmeticFunction.coe_mk, ite_eq_left hsq, hcard, hsieve]
      exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) (card_le_card hsub)
    · simpa [roughSquarefreeWeight, squarefreeWeight, hd, hsq] using sievedCoefficientWeight_nonneg P Z n
  · simpa [roughSquarefreeWeight, hd] using sievedCoefficientWeight_nonneg P Z n

theorem coefficientWeight_le_sieved (B Z n : ℕ) :
    coefficientWeight B n ≤ coefficientScale B * sievedCoefficientWeight (auxiliaryCutoff B) Z n :=
  mul_le_mul_of_nonneg_left (roughSquarefreeWeight_le_sieved _ _ _) (coefficientScale_nonneg B)

theorem coefficient_triple_le_sieved (B Z j b c : ℕ) :
    coefficientWeight B b * coefficientWeight B c * coefficientWeight B (b + j * c) ≤
      coefficientScale B ^ 3 *
        threeFormSieveWeight (sievePrimes Z) (roughSieveTheta (auxiliaryCutoff B)) j b c := by
  have h := mul_le_mul
    (mul_le_mul (coefficientWeight_le_sieved B Z b) (coefficientWeight_le_sieved B Z c)
      (coefficientWeight_nonneg B c)
      (mul_nonneg (coefficientScale_nonneg B) (sievedCoefficientWeight_nonneg _ _ _)))
    (coefficientWeight_le_sieved B Z (b + j * c)) (coefficientWeight_nonneg B (b + j * c))
    (mul_nonneg (mul_nonneg (coefficientScale_nonneg B) (sievedCoefficientWeight_nonneg _ _ _))
      (mul_nonneg (coefficientScale_nonneg B) (sievedCoefficientWeight_nonneg _ _ _)))
  apply h.trans_eq
  simp only [sievedCoefficientWeight, threeFormSieveWeight, Nat.cast_add, Nat.cast_mul,
    prod_mul_distrib]
  ring

end JointDickman

end OAI
