import OAI.NumberTheory.JointDickman.Probability.ArithmeticSplitWeights

namespace OAI

/-! # Nonzero coefficients on the application range are auxiliary-prime products -/

namespace JointDickman
open Finset

open Classical in
theorem coefficientWeight_prime_support {B n : ℕ}
    (hn : coefficientWeight B n ≠ 0) (hsize : (n : ℝ) ≤ auxiliaryUpper B) :
    Squarefree n ∧ n.primeFactors ⊆ auxiliaryPrimes B := by
  have hrough : Disjoint n.primeFactors (Nat.primesLE (auxiliaryCutoff B)) := by
    by_contra hd
    exact hn (by simp [coefficientWeight,roughSquarefreeWeight,hd])
  have hsq : Squarefree n := by
    by_contra hs
    exact hn (by simp [coefficientWeight,roughSquarefreeWeight,squarefreeWeight,hs])
  refine ⟨hsq,?_⟩
  intro p hp
  have hprime := (Nat.mem_primeFactors.mp hp).1
  have hpn := Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) (Nat.mem_primeFactors.mp hp).2.1
  have hlarge : auxiliaryCutoff B < p := by
    by_contra h
    exact disjoint_left.mp hrough hp (Nat.mem_primesLE.mpr ⟨by omega,hprime⟩)
  change p ∈ largePrimeSet (auxiliaryUpper B) (auxiliaryCutoff B)
  apply mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩,?_⟩
  · exact (Nat.le_floor_iff (le_trans (Nat.cast_nonneg n) hsize)).mpr
      ((by exact_mod_cast hpn : (p : ℝ) ≤ n).trans hsize)
  · exact_mod_cast hlarge

open Classical in
theorem coefficientWeight_eq_primeProduct {B n : ℕ}
    (hn : coefficientWeight B n ≠ 0) (hsize : (n : ℝ) ≤ auxiliaryUpper B) :
    n = ∏ p ∈ coefficientPrimeSet B n,p := by
  obtain ⟨hsq,hsub⟩ := coefficientWeight_prime_support hn hsize
  rw [coefficientPrimeSet_eq_inter hsq.ne_zero,inter_eq_left.mpr hsub]
  exact (Nat.prod_primeFactors_of_squarefree hsq).symm

/-- The elementary global cap used only for the rare common-prime error. -/
theorem coefficientWeight_le_scale (B n : ℕ) : coefficientWeight B n ≤ coefficientScale B := by
  classical
  have h : roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1/2) n ≤ (1 : ℝ) := by
    unfold roughSquarefreeWeight squarefreeWeight
    simp only [ArithmeticFunction.coe_mk]
    split_ifs
    · exact pow_le_one₀ (by norm_num) (by norm_num)
    all_goals norm_num
  exact (mul_le_mul_of_nonneg_left h (coefficientScale_nonneg B)).trans_eq (mul_one _)

end JointDickman

end OAI
