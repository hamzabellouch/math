import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCoverage

namespace OAI

/-! The actual finite harmonic mass in the manuscript's half-open bins.
Its lower bound follows from the proved reciprocal padding law and its
upper bound simply removes the two restrictions. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def paddingPairHarmonicMass (Q : Finset ℕ) (L η : ℝ) (d : ℕ) : ℝ :=
  ∑ q ∈ retainedPrimeDivisors Q,
    if PaddingPairEligible L η d q then
      (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0

/-- This is the literal `S₀`: the index restriction is on the left endpoint
of each bin, exactly as in `q:bins`. -/
noncomputable def totalPaddingBinMass (D Q : Finset ℕ) (L η : ℝ) : ℝ :=
  ∑ j ∈ paddingBinIndices L η, ∑ d ∈ D, ∑ q ∈ retainedPrimeDivisors Q,
    if (q.primeFactors.card : ℝ) ≤ 100 * Real.log L ∧
        (j : ℝ) * η ≤ Real.log (d * q : ℕ) ∧
        Real.log (d * q : ℕ) < ((j : ℝ) + 1) * η
    then (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0

lemma padding_bin_weight_sum (L η : ℝ) (d q : ℕ) (hη : 0 < η) :
    (∑ j ∈ paddingBinIndices L η,
      if (q.primeFactors.card : ℝ) ≤ 100 * Real.log L ∧
          (j : ℝ) * η ≤ Real.log (d * q : ℕ) ∧
          Real.log (d * q : ℕ) < ((j : ℝ) + 1) * η
      then (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0) =
      if PaddingPairEligible L η d q then
        (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0 := by
  have hi (j : ℤ) :
      ((j : ℝ) * η ≤ Real.log (d * q : ℕ) ∧
        Real.log (d * q : ℕ) < ((j : ℝ) + 1) * η) ↔
        paddingBin η 0 (Real.log (d * q : ℕ)) = j := by
    simpa only [add_zero] using
      (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).symm
  simp only [hi, PaddingPairEligible]
  by_cases hc : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L
  · simp [hc]
  · simp [hc]

lemma totalPaddingBinMass_eq (D Q : Finset ℕ) (L η : ℝ) (hη : 0 < η) :
    totalPaddingBinMass D Q L η = ∑ d ∈ D, paddingPairHarmonicMass Q L η d := by
  unfold totalPaddingBinMass paddingPairHarmonicMass
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  exact padding_bin_weight_sum L η d q hη

lemma paddingPairHarmonicMass_probability (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (L η : ℝ) (d : ℕ) :
    paddingPairHarmonicMass Q L η d =
      (paddingTiltNormalizer Q / d) * (reciprocalPaddingLaw Q).probability
        (fun b => PaddingPairEligible L η d (paddingSelectedDivisor Q b)) := by
  let T : ℝ := ∑ q ∈ retainedPrimeDivisors Q,
    ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) *
      (if PaddingPairEligible L η d q then 1 else 0)
  have hP := reciprocal_padding_average Q hQ
    (fun q => if PaddingPairEligible L η d q then 1 else 0)
  change (reciprocalPaddingLaw Q).probability
    (fun b => PaddingPairEligible L η d (paddingSelectedDivisor Q b)) =
      (paddingTiltNormalizer Q)⁻¹ * T at hP
  have he : paddingPairHarmonicMass Q L η d = (1 / (d : ℝ)) * T := by
    unfold paddingPairHarmonicMass T
    rw [mul_sum]
    apply sum_congr rfl
    intro q _
    by_cases h : PaddingPairEligible L η d q
    · simp only [ite_eq_left h, mul_one, Nat.cast_mul]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp only [ite_eq_right h, mul_zero]
  rw [he, hP]
  have hS := paddingTiltNormalizer_pos Q
  simp only [div_eq_mul_inv, one_mul]
  symm
  calc
    _ = (paddingTiltNormalizer Q * (paddingTiltNormalizer Q)⁻¹) *
        ((d : ℝ)⁻¹ * T) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hS.ne', one_mul]

lemma paddingPairHarmonicMass_bounds (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {L η : ℝ} (hη : 0 < η)
    (hhalf : (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw Q).probability
      (fun b => booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L))
    (d : ℕ) (hd : 0 < d) (hdL : Real.log d ≤ 2 * L) :
    (paddingTiltNormalizer Q / d) * (1 / 2) ≤ paddingPairHarmonicMass Q L η d ∧
      paddingPairHarmonicMass Q L η d ≤ paddingTiltNormalizer Q / d := by
  rw [paddingPairHarmonicMass_probability Q hQ]
  have hfactor : 0 ≤ paddingTiltNormalizer Q / (d : ℝ) :=
    div_nonneg (paddingTiltNormalizer_pos Q).le (Nat.cast_nonneg d)
  constructor
  · exact mul_le_mul_of_nonneg_left
      (reciprocal_padding_eligible_probability Q hQ hη hhalf d hd hdL) hfactor
  · exact (mul_le_mul_of_nonneg_left
      ((reciprocalPaddingLaw Q).probability_le_one _) hfactor).trans_eq (mul_one _)

theorem totalPaddingBinMass_bounds (D Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {L η : ℝ} (hη : 0 < η)
    (hhalf : (1 / 2 : ℝ) ≤ (reciprocalPaddingLaw Q).probability
      (fun b => booleanCount b ≤ 100 * Real.log L ∧ paddingLog Q b ≤ 98 * L))
    (hD : ∀ d ∈ D, 0 < d ∧ Real.log d ≤ 2 * L) :
    (1 / 2 : ℝ) * paddingTiltNormalizer Q * (∑ d ∈ D, 1 / (d : ℝ)) ≤
        totalPaddingBinMass D Q L η ∧
      totalPaddingBinMass D Q L η ≤
        paddingTiltNormalizer Q * (∑ d ∈ D, 1 / (d : ℝ)) := by
  rw [totalPaddingBinMass_eq D Q L η hη]
  have hl : (1 / 2 : ℝ) * paddingTiltNormalizer Q * (∑ d ∈ D, 1 / (d : ℝ)) =
      ∑ d ∈ D, (paddingTiltNormalizer Q / d) * (1 / 2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro d _
    ring
  have hu : paddingTiltNormalizer Q * (∑ d ∈ D, 1 / (d : ℝ)) =
      ∑ d ∈ D, paddingTiltNormalizer Q / d := by
    rw [mul_sum]
    apply sum_congr rfl
    intro d _
    ring
  rw [hl, hu]
  constructor
  · exact sum_le_sum fun d hd =>
      (paddingPairHarmonicMass_bounds Q hQ hη hhalf d (hD d hd).1 (hD d hd).2).1
  · exact sum_le_sum fun d hd =>
      (paddingPairHarmonicMass_bounds Q hQ hη hhalf d (hD d hd).1 (hD d hd).2).2

/-- The manuscript's retained bin mass bound, uniform over every finite
centered divisor family with the proved logarithmic size restriction. -/
theorem ModFiveThetaInput.eventually_totalPaddingBinMass (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (D : Finset ℕ) (η : ℝ), 0 < η →
      (∀ d ∈ D, 0 < d ∧ Real.log d ≤ 2 * L) →
      (1 / 2 : ℝ) * paddingTiltNormalizer (paddingPrimeSupply E L) *
          (∑ d ∈ D, 1 / (d : ℝ)) ≤ totalPaddingBinMass D (paddingPrimeSupply E L) L η ∧
        totalPaddingBinMass D (paddingPrimeSupply E L) L η ≤
          paddingTiltNormalizer (paddingPrimeSupply E L) * (∑ d ∈ D, 1 / (d : ℝ)) := by
  filter_upwards [hP.eventually_retained_padding_probability E] with L hL
  intro D η hη hD
  exact totalPaddingBinMass_bounds D _ (fun _ hp => paddingPrimeSupply_prime hp) hη hL hD

end TwoPointCorrelations

end OAI
