import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Compatibility
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy

namespace OAI

/-! Fixed rational distributions and their entropy and capacity formulas. -/

namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

theorem entropy_two_points {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A) (hab : a ≠ b) (p q : ℝ) :
    finiteEntropy (fun i => if i = a then p else if i = b then q else 0) =
      entropyTerm p + entropyTerm q := by
  unfold finiteEntropy
  calc
    _ = ∑ i : A, ((if i = a then entropyTerm p else 0) +
        (if i = b then entropyTerm q else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = a
      · subst i
        simp [hab]
      · by_cases hj : i = b
        · subst i
          simp [hab.symm]
        · simp [hi, hj]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem weighted_two_points {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A) (hab : a ≠ b) (p q : ℝ) (f : A → ℝ) :
    (∑ i : A, (if i = a then p else if i = b then q else 0) * f i) =
      p * f a + q * f b := by
  calc
    _ = ∑ i : A, ((if i = a then p * f a else 0) +
        (if i = b then q * f b else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = a
      · subst i
        simp [hab]
      · by_cases hj : i = b
        · subst i
          simp [hi]
        · simp [hi, hj]
    _ = _ := by simp [Finset.sum_add_distrib]

def statisticRate (d : ℚ) (k : Fin 5) : ℝ :=
  finiteEntropy (fun i : Fin 6 => (statisticLaw d k i : ℝ)) +
    ∑ i : Fin 6, (statisticLaw d k i : ℝ) * Real.log (multiplicity i : ℝ)

def binaryEntropyRate (d : ℚ) : ℝ :=
  entropyTerm (1 - (d : ℝ)) + entropyTerm (d : ℝ) + (d : ℝ) * Real.log 2

theorem statisticLaw_two_real (d : ℚ) (i : Fin 6) :
    (statisticLaw d 2 i : ℝ) =
      if i = 2 then 1 - (d : ℝ) else if i = 3 then (d : ℝ) else 0 := by
  by_cases hi : i = 2
  · simp [statisticLaw, hi]
  · by_cases hj : i = 3 <;> simp [statisticLaw, hi, hj]

theorem statisticRate_two (d : ℚ) :
    statisticRate d 2 = binaryEntropyRate d + 2 * (1 - (d : ℝ)) * Real.log 5 := by
  unfold statisticRate
  simp_rw [statisticLaw_two_real]
  rw [entropy_two_points (2 : Fin 6) 3 (by decide),
    weighted_two_points (2 : Fin 6) 3 (by decide)]
  have h25 : Real.log (25 : ℝ) = 2 * Real.log 5 := by
    have hp : (5 : ℝ) ^ 2 = 25 := by norm_num
    rw [← hp, Real.log_pow]
    norm_num
  change entropyTerm (1 - (d : ℝ)) + entropyTerm (d : ℝ) +
    ((1 - (d : ℝ)) * Real.log 25 + (d : ℝ) * Real.log 2) = _
  rw [h25]
  unfold binaryEntropyRate
  ring

theorem statisticRate_deterministic (d : ℚ) (k : Fin 5) (hk : k.val ≠ 2) :
    statisticRate d k = Real.log (multiplicity (singletonSlot k.val) : ℝ) := by
  have hmass (i : Fin 6) : (statisticLaw d k i : ℝ) =
      if i = singletonSlot k.val then 1 else 0 := by
    by_cases hi : i = singletonSlot k.val <;> simp [statisticLaw, hk, hi]
  unfold statisticRate finiteEntropy
  simp_rw [hmass]
  simp [entropyTerm, apply_ite]

theorem statisticRate_zero (d : ℚ) : statisticRate d 0 = 0 := by
  rw [statisticRate_deterministic d 0 (by decide)]
  norm_num [singletonSlot, multiplicity]

theorem statisticRate_one (d : ℚ) : statisticRate d 1 = Real.log 10 := by
  rw [statisticRate_deterministic d 1 (by decide)]
  norm_num [singletonSlot, multiplicity]

theorem statisticRate_three (d : ℚ) : statisticRate d 3 = Real.log 10 := by
  rw [statisticRate_deterministic d 3 (by decide)]
  change Real.log (10 : ℝ) = Real.log 10
  rfl

theorem statisticRate_four (d : ℚ) : statisticRate d 4 = 0 := by
  rw [statisticRate_deterministic d 4 (by decide)]
  have hv : multiplicity (singletonSlot (4 : Fin 5).val) = 1 := by decide +kernel
  rw [hv]
  norm_num

end

end MatrixMultiplication.AllFieldParameters

end OAI
