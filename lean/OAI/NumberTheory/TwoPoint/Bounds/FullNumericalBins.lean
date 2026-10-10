import OAI.NumberTheory.TwoPoint.Bounds.FullDivisibilityFamily
import OAI.NumberTheory.TwoPoint.Bounds.NumericalBins

namespace OAI

/-! The full-divisibility main term on the exact retained numerical pairs,
with its original harmonic mass and real bin endpoint. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def numericalBinPairs (D R : Finset ℕ) (L η : ℝ) (j : ℤ) : Finset (ℕ × ℕ) :=
  (D ×ˢ R).filter (fun e => numericalBinEligible L η j e.1 e.2)

noncomputable def numericalBinHarmonicMass (D R : Finset ℕ) (L η : ℝ) (j : ℤ) : ℝ :=
  ∑ e ∈ numericalBinPairs D R L η j, actualPaddingCoefficient e.2 / (e.1 * e.2 : ℕ)

noncomputable def fullNumericalBin (D R : Finset ℕ) (L η : ℝ) (j : ℤ)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ) (T : ℝ) : ℂ :=
  ∑ e ∈ numericalBinPairs D R L η j, (actualPaddingCoefficient e.2 : ℂ) *
    (positivePrefix (fullLiouvilleProfile l b (e.2 * e.1) h) ⌊T⌋₊ / (T : ℂ))

lemma numericalBinHarmonicMass_nonneg (D R : Finset ℕ) (L η : ℝ) (j : ℤ) :
    0 ≤ numericalBinHarmonicMass D R L η j := by
  apply sum_nonneg
  intro e _
  exact div_nonneg (actualPaddingCoefficient_nonneg _) (Nat.cast_nonneg _)

lemma fullNumericalBin_error (D R : Finset ℕ) (L η X : ℝ)
    (hX : 0 < X) (hη : 0 ≤ η) (j : ℤ)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ)
    (hunit : ∀ d ∈ D, ∀ q ∈ R, IsUnit ((q * d : ℕ) : ZMod l)) :
    ‖fullNumericalBin D R L η j l b h (X * Real.exp ((j : ℝ) * η)) -
      (numericalBinHarmonicMass D R L η j : ℂ) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊X⌋₊ / (X : ℂ))‖ ≤
      numericalBinHarmonicMass D R L η j * (2 * η + 1 / X) := by
  have he (e : ℕ × ℕ) (he : e ∈ numericalBinPairs D R L η j) :
      e.1 ∈ D ∧ e.2 ∈ R ∧ numericalBinEligible L η j e.1 e.2 := by
    simpa only [numericalBinPairs, mem_filter, mem_product, and_assoc] using he
  have hb := full_divisibility_family_error l b h (numericalBinPairs D R L η j)
    (fun e => e.2 * e.1) (fun e => actualPaddingCoefficient e.2)
    (fun e _ => actualPaddingCoefficient_nonneg e.2)
    (fun e he' => Nat.mul_pos (he e he').2.2.2.1 (he e he').2.2.1)
    (fun e he' => hunit e.1 (he e he').1 e.2 (he e he').2.1)
    X (X * Real.exp ((j : ℝ) * η)) η hX hη
    (fun e he' => by
      simpa only [Nat.mul_comm] using (actualPaddingBin_cutoff e.1 e.2
        (he e he').2.2.1 (he e he').2.2.2.1 η X hX j (he e he').2.2.2.2.2).1)
    (fun e he' => by
      simpa only [Nat.mul_comm] using (actualPaddingBin_cutoff e.1 e.2
        (he e he').2.2.1 (he e he').2.2.2.1 η X hX j (he e he').2.2.2.2.2).2)
  simpa only [fullNumericalBin, numericalBinHarmonicMass, Nat.mul_comm] using hb

lemma numericalBinHarmonicMass_total (D Q : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d) (hQ : ∀ p ∈ Q, p.Prime)
    (L η : ℝ) (hL : 1 ≤ L) :
    (∑ j ∈ paddingBinIndices L η,
      numericalBinHarmonicMass D (boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊) L η j) =
      totalPaddingBinMass D Q L η := by
  simp only [numericalBinHarmonicMass, numericalBinPairs, sum_filter, sum_product]
  exact numericalBin_mass D Q hD hQ L η hL

theorem fullNumericalBins_error (D Q : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d) (hQ : ∀ p ∈ Q, p.Prime)
    (L η X : ℝ) (hL : 1 ≤ L) (hX : 0 < X) (hη : 0 ≤ η)
    (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ)
    (hunit : ∀ d ∈ D, ∀ q ∈ boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊,
      IsUnit ((q * d : ℕ) : ZMod l)) :
    ‖(∑ j ∈ paddingBinIndices L η,
        fullNumericalBin D (boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊) L η j l b h
          (X * Real.exp ((j : ℝ) * η))) -
      (totalPaddingBinMass D Q L η : ℂ) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊X⌋₊ / (X : ℂ))‖ ≤
      totalPaddingBinMass D Q L η * (2 * η + 1 / X) := by
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let F := positivePrefix
    (fun n => progressionSequence liouville l b n * liouville (n + h)) ⌊X⌋₊ / (X : ℂ)
  have hm := numericalBinHarmonicMass_total D Q hD hQ L η hL
  have he : (∑ j ∈ paddingBinIndices L η,
      fullNumericalBin D R L η j l b h (X * Real.exp ((j : ℝ) * η))) -
      (totalPaddingBinMass D Q L η : ℂ) * F =
      ∑ j ∈ paddingBinIndices L η,
        (fullNumericalBin D R L η j l b h (X * Real.exp ((j : ℝ) * η)) -
          (numericalBinHarmonicMass D R L η j : ℂ) * F) := by
    rw [← hm]
    push_cast
    rw [sum_sub_distrib, sum_mul]
  change ‖_ - _ * F‖ ≤ _
  rw [he]
  calc
    _ ≤ ∑ j ∈ paddingBinIndices L η,
        ‖fullNumericalBin D R L η j l b h (X * Real.exp ((j : ℝ) * η)) -
          (numericalBinHarmonicMass D R L η j : ℂ) * F‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ paddingBinIndices L η,
        numericalBinHarmonicMass D R L η j * (2 * η + 1 / X) :=
      sum_le_sum (fun j _ => fullNumericalBin_error D R L η X hX hη j l b h hunit)
    _ = _ := by rw [← sum_mul, hm]

end TwoPointCorrelations

end OAI
