import OAI.NumberTheory.JointDickman.Arithmetic.RegularPrimeSets
import OAI.NumberTheory.JointDickman.Arithmetic.MixedThreeFormSieve

namespace OAI

/-! # Exponential prime-count tilts of the actual coefficient -/

namespace JointDickman

open Finset

noncomputable def primeDivisorCount (Q : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactors ∩ Q).card

noncomputable def tiltedPrimeWeight (Q : Finset ℕ) (s : ℝ) (p : ℕ) : ℝ :=
  if p ∈ Q then (1 / 2 : ℝ) * Real.exp s else 1 / 2

noncomputable def tiltedCoefficientWeight (B : ℕ) (Q : Finset ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  coefficientWeight B n * Real.exp (s * primeDivisorCount Q n)

noncomputable def tiltedSieveTheta (P : ℕ) (Q : Finset ℕ) (s : ℝ) (p : ℕ) : ℝ :=
  if p ≤ P then 0 else tiltedPrimeWeight Q s p

theorem coefficient_prefix_count {B n : ℕ} (hn : n ≠ 0) (g : ℝ) :
    (primePrefix B g (coefficientPrimeSet B n)).card =
      primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) n := by
  rw [coefficientPrimeSet_eq_inter hn, primePrefix_inter]
  rfl

theorem coefficient_tail_count {B n : ℕ} (hn : n ≠ 0) (Y : ℝ) :
    ((coefficientPrimeSet B n).filter (fun p : ℕ => Y < Real.log p)).card =
      primeDivisorCount ((auxiliaryPrimes B).filter (fun p : ℕ => Y < Real.log p)) n := by
  classical
  rw [coefficientPrimeSet_eq_inter hn]
  congr 1
  ext p
  simp only [mem_filter, mem_inter]
  tauto

@[simp] theorem coefficientWeight_zero (B : ℕ) : coefficientWeight B 0 = 0 := by
  simp [coefficientWeight, roughSquarefreeWeight, squarefreeWeight]

theorem tiltedPrimeWeight_bounds (Q : Finset ℕ) {s : ℝ} (hs : Real.exp s ≤ 2) (p : ℕ) :
    0 ≤ tiltedPrimeWeight Q s p ∧ tiltedPrimeWeight Q s p ≤ 1 := by
  unfold tiltedPrimeWeight
  split_ifs <;> constructor <;> nlinarith [Real.exp_pos s]

theorem tiltedSieveTheta_bounds (P : ℕ) (Q : Finset ℕ) {s : ℝ} (hs : Real.exp s ≤ 2) (p : ℕ) :
    0 ≤ tiltedSieveTheta P Q s p ∧ tiltedSieveTheta P Q s p ≤ 1 := by
  unfold tiltedSieveTheta
  split_ifs
  · norm_num
  · exact tiltedPrimeWeight_bounds Q hs p

theorem tilted_prime_product (S Q : Finset ℕ) (s : ℝ) :
    (∏ p ∈ S, tiltedPrimeWeight Q s p) =
      (1 / 2 : ℝ) ^ S.card * Real.exp (s * (S ∩ Q).card) := by
  classical
  have heq (p : ℕ) : tiltedPrimeWeight Q s p =
      (1 / 2 : ℝ) * (if p ∈ Q then Real.exp s else 1) := by
    by_cases hp : p ∈ Q <;> simp [tiltedPrimeWeight, hp]
  have hfilter : S.filter (fun p => p ∈ Q) = S ∩ Q := by ext p; simp
  simp_rw [heq]
  rw [prod_mul_distrib, prod_const, ← prod_filter, hfilter, prod_const, ← Real.exp_nat_mul]
  congr 2; ring

theorem tiltedCoefficientWeight_nonneg (B : ℕ) (Q : Finset ℕ) (s : ℝ) (n : ℕ) :
    0 ≤ tiltedCoefficientWeight B Q s n :=
  mul_nonneg (coefficientWeight_nonneg _ _) (Real.exp_pos _).le

theorem tiltedCoefficientWeight_le_sieved (B Z : ℕ) (Q : Finset ℕ) {s : ℝ}
    (hs : Real.exp s ≤ 2) (n : ℕ) :
    tiltedCoefficientWeight B Q s n ≤ coefficientScale B *
      ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) := by
  classical
  have hnonneg : 0 ≤ coefficientScale B *
      ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) :=
    mul_nonneg (coefficientScale_nonneg _) (prod_nonneg (fun p _ =>
      residueWeight_nonneg _ _ (tiltedSieveTheta_bounds _ Q hs p).1))
  by_cases hd : Disjoint n.primeFactors (Nat.primesLE (auxiliaryCutoff B))
  · by_cases hsq : Squarefree n
    · have hcard : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
        calc
          _ = ArithmeticFunction.cardFactors (∏ p ∈ n.primeFactors, p) :=
            congrArg ArithmeticFunction.cardFactors (Nat.prod_primeFactors_of_squarefree hsq).symm
          _ = _ := primeProduct_cardFactors _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
      have heq (p : ℕ) (hp : p ∈ sievePrimes Z) :
          residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) =
            if p ∣ n then tiltedPrimeWeight Q s p else 1 := by
        have hpprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
        by_cases hpn : p ∣ n
        · have hpP : ¬p ≤ auxiliaryCutoff B := by
            intro h
            exact disjoint_left.mp hd (hpprime.mem_primeFactors hpn hsq.ne_zero)
              (Nat.mem_primesLE.mpr ⟨h, hpprime⟩)
          simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn, tiltedSieveTheta, hpP]
        · simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn]
      have hsub : (sievePrimes Z).filter (fun p => p ∣ n) ⊆ n.primeFactors := by
        intro p hp
        have hmem := mem_filter.mp hp
        exact (Nat.mem_primesLE.mp (mem_filter.mp hmem.1).1).2.mem_primeFactors hmem.2 hsq.ne_zero
      have hprod : (∏ p ∈ n.primeFactors, tiltedPrimeWeight Q s p) ≤
          ∏ p ∈ (sievePrimes Z).filter (fun p => p ∣ n), tiltedPrimeWeight Q s p :=
        prod_le_prod_of_subset_of_le_one₀ hsub
          (fun p _ => (tiltedPrimeWeight_bounds Q hs p).1)
          (fun p _ _ => (tiltedPrimeWeight_bounds Q hs p).2)
      have htprod := tilted_prime_product n.primeFactors Q s
      rw [htprod] at hprod
      have hbound := mul_le_mul_of_nonneg_left hprod (coefficientScale_nonneg B)
      simpa only [tiltedCoefficientWeight, coefficientWeight, roughSquarefreeWeight,
        ArithmeticFunction.coe_mk, ite_eq_left hd, squarefreeWeight, ite_eq_left hsq,
        hcard, primeDivisorCount, mul_assoc, prod_congr rfl heq, ← prod_filter] using hbound
    · simpa [tiltedCoefficientWeight, coefficientWeight, roughSquarefreeWeight, squarefreeWeight, hd, hsq] using hnonneg
  · simpa [tiltedCoefficientWeight, coefficientWeight, roughSquarefreeWeight, hd] using hnonneg

end JointDickman

end OAI
