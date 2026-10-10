import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinMassTotal
import OAI.NumberTheory.TwoPoint.Bounds.BinCutoffGeometry
import OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool

namespace OAI

/-! One common eligibility predicate for the literal manuscript bins.
Positivity makes the log-product identity valid even outside the prime pools. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def numericalBinEligible (L η : ℝ) (j : ℤ) (d q : ℕ) : Prop :=
  0 < d ∧ 0 < q ∧ (q.primeFactors.card : ℝ) ≤ 100 * Real.log L ∧
    actualPaddingBin η (Real.log d) j q

lemma numericalBinEligible_bin (L η : ℝ) (j : ℤ) (d q : ℕ)
    (he : numericalBinEligible L η j d q) : actualPaddingBin η (Real.log d) j q := he.2.2.2

lemma numericalBinEligible_pair (L η : ℝ) (hη : 0 < η) (j : ℤ)
    (hj : j ∈ paddingBinIndices L η) (d q : ℕ) (he : numericalBinEligible L η j d q) :
    PaddingPairEligible L η d q := by
  refine ⟨he.2.2.1, ?_⟩
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast he.1.ne'
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast he.2.1.ne'
  have hlog : Real.log (d * q : ℕ) = Real.log q + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul hd hq]
    ring
  have hb : paddingBin η 0 (Real.log (d * q : ℕ)) = j := by
    apply (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).mpr
    simpa only [actualPaddingBin, hlog, add_zero] using he.2.2.2
  rw [hb]
  exact hj

lemma numericalBin_mass (D Q : Finset ℕ) (hD : ∀ d ∈ D, 0 < d)
    (hQ : ∀ p ∈ Q, p.Prime) (L η : ℝ) (hL : 1 ≤ L) :
    (∑ j ∈ paddingBinIndices L η, ∑ d ∈ D,
      ∑ q ∈ boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊,
        if numericalBinEligible L η j d q then
          actualPaddingCoefficient q / (d * q : ℕ) else 0) =
      totalPaddingBinMass D Q L η := by
  unfold totalPaddingBinMass boundedPaddingDivisors
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro d hd
  rw [sum_filter]
  apply sum_congr rfl
  intro q hq
  have hqp := retainedPrimeDivisor_pos Q hQ hq
  have hr : q.primeFactors.card ≤ ⌊100 * Real.log L⌋₊ ↔
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L :=
    Nat.le_floor_iff (mul_nonneg (by norm_num) (Real.log_nonneg hL))
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (hD d hd).ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqp.ne'
  have hlog : Real.log (d * q : ℕ) = Real.log q + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul hd0 hq0]
    ring
  simp only [hr, numericalBinEligible, hD d hd, hqp, true_and, actualPaddingBin,
    actualPaddingCoefficient, hlog]
  split_ifs <;> simp_all

end TwoPointCorrelations

end OAI
