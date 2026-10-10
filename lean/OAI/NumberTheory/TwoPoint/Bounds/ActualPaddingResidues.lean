import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingWeights
import OAI.NumberTheory.TwoPoint.Bounds.PaddingDegreeTail
import OAI.NumberTheory.TwoPoint.Bounds.PaddingLargeBinCut

namespace OAI

/-! The proved padding laws applied to the graph's actual integer
normalization and bin density at any common lift of the prime residues. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma actualPaddingAvailability_lift (Q : Finset ℕ) (B : ℕ) (site : ℤ)
    (z : Q → Fin B) (n : ℤ)
    (hn : ∀ p : Q, (n : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val)) :
    (fun p : Q => decide ((p.val : ℤ) ∣ n)) = paddingResidueAvailable Q B site z := by
  funext p
  have hd : (p.val : ℤ) ∣ n ↔ (p.val : ℤ) ∣ ((z p).val : ℤ) + site := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_add, Int.cast_natCast, hn p]
  simp only [paddingResidueAvailable, hd]

lemma actualPaddingWeight_lift (Q : Finset ℕ) (B : ℕ) (site : ℤ)
    (z : Q → Fin B) (n : ℤ)
    (hn : ∀ p : Q, (n : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val)) :
    actualPaddingWeight Q n = paddingTiltWeight Q (paddingResidueAvailable Q B site z) := by
  rw [actualPaddingWeight_eq_tilt, actualPaddingAvailability_lift Q B site z n hn]

lemma actualPaddingDegree_lift (Q : Finset ℕ) (B : ℕ) (site : ℤ)
    (z : Q → Fin B) (n : ℤ)
    (hn : ∀ p : Q, (n : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val)) :
    (actualPaddingDegree Q n : ℝ) = booleanCount (paddingResidueAvailable Q B site z) := by
  rw [actualPaddingDegree_eq_available, actualPaddingAvailability_lift Q B site z n hn,
    paddingAvailablePrimes_card, booleanCount_eq_card]
  rfl

lemma actualPaddingBin_lift (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (B : ℕ) (site : ℤ) (z : Q → Fin B) (n : ℤ)
    (hn : ∀ p : Q, (n : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val))
    (η c : ℝ) (j : ℤ) (hη : 0 < η) :
    integerPaddingBinMass Q n η c j =
      literalPaddingBinMass Q (paddingResidueAvailable Q B site z) η c j := by
  rw [← literalPaddingBinMass_integer Q hQ n η c j hη,
    actualPaddingAvailability_lift Q B site z n hn]

/-- The literal graph density, including an arbitrary restriction on the
padding-divisor set, has the same squared-bin bound at any residue lift. -/
theorem ModFiveThetaInput.actual_padding_residue_bin_square (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c : ℝ) (B : ℕ) (site : ℤ) (bins : Finset ℤ),
      1 ≤ L → 0 < η → η ≤ 1 →
      ∀ (hQB : ∀ p ∈ paddingPrimeSupply E L, p ≤ B)
        (D : Finset ℕ), D ⊆ retainedPrimeDivisors (paddingPrimeSupply E L) →
      ∀ N : (paddingPrimeSupply E L → Fin B) → ℤ,
      (∀ z (p : paddingPrimeSupply E L),
        (N z : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val)) →
      (FiniteLaw.independent (fun p : paddingPrimeSupply E L =>
        uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos
          (hQB p p.property))).average (fun z =>
            (actualPaddingVertex (paddingPrimeSupply E L) (N z)) ^ 2 *
              ∑ j ∈ bins, (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
                (actualPaddingVertex (paddingPrimeSupply E L)) (N z)) ^ 2) /
                  paddingTiltNormalizer (paddingPrimeSupply E L) ≤ C / L := by
  obtain ⟨C, hC, hb⟩ := hP.padding_residue_bin_square E
  refine ⟨C, hC, ?_⟩
  intro L η c B site bins hL hη hηone hQB D hD N hN
  let Q := paddingPrimeSupply E L
  let μ := FiniteLaw.independent (fun p : Q =>
    uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos (hQB p p.property))
  calc
    _ ≤ μ.average (fun z => paddingTiltWeight Q (paddingResidueAvailable Q B site z) *
        ∑ j ∈ bins, (literalPaddingBinMass Q (paddingResidueAvailable Q B site z) η c j) ^ 2) /
          paddingTiltNormalizer Q := by
      apply div_le_div_of_nonneg_right _ (paddingTiltNormalizer_pos Q).le
      apply μ.average_mono
      intro z
      rw [actualPaddingVertex_sq, actualPaddingWeight_lift Q B site z (N z) (hN z)]
      apply mul_le_mul_of_nonneg_left _ (paddingTiltWeight_pos Q _).le
      apply sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (actualPaddingDensity_nonneg Q D (actualPaddingBin η c j) (N z))
      exact (actualPaddingDensity_le_integerBin Q D hD (N z) η c j).trans_eq
        (actualPaddingBin_lift Q (fun _ hp => paddingPrimeSupply_prime hp)
          B site z (N z) (hN z) η c j hη)
    _ ≤ C / L := hb L η c B site bins hL hη hηone hQB

/-- Deleting vertices with more than `400 log L` padding primes has the
proved weighted probability cost for the literal graph normalization. -/
theorem ModFiveThetaInput.eventually_actual_padding_degree_tail (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (site : ℤ)
      (hQB : ∀ p ∈ paddingPrimeSupply E L, p ≤ B)
      (N : (paddingPrimeSupply E L → Fin B) → ℤ),
      (∀ z (p : paddingPrimeSupply E L),
        (N z : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val)) →
      (FiniteLaw.independent (fun p : paddingPrimeSupply E L =>
        uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos
          (hQB p p.property))).average (fun z =>
            (actualPaddingVertex (paddingPrimeSupply E L) (N z)) ^ 2 *
              if ¬actualPaddingDegreeCut (paddingPrimeSupply E L) L (N z) then 1 else 0) /
                paddingTiltNormalizer (paddingPrimeSupply E L) ≤ L ^ (-100 : ℝ) := by
  filter_upwards [hP.eventually_padding_residue_degree_tail E] with L hL
  intro B site hQB N hN
  have he (z : paddingPrimeSupply E L → Fin B) :
      (actualPaddingVertex (paddingPrimeSupply E L) (N z)) ^ 2 *
          (if ¬actualPaddingDegreeCut (paddingPrimeSupply E L) L (N z) then 1 else 0) =
        paddingTiltWeight _ (paddingResidueAvailable _ B site z) *
          (if 400 * Real.log L < booleanCount (paddingResidueAvailable _ B site z)
            then 1 else 0) := by
    rw [actualPaddingVertex_sq, actualPaddingWeight_lift _ B site z (N z) (hN z)]
    simp only [actualPaddingDegreeCut, actualPaddingDegree_lift _ B site z (N z) (hN z), not_le]
  simp_rw [he]
  exact hL B site hQB

end TwoPointCorrelations

end OAI
