import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCriticalMass

namespace OAI

/-! # Counting the integral alternative at actual L-function zeros -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators Classical

 theorem density_count_cube (R I K D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hlower : R ≤ K * I) (hfourth : I ^ 4 ≤ R * D) : R ^ 3 ≤ K ^ 4 * D := by
  by_cases hzero : R = 0
  · simpa only [hzero, zero_pow (by decide : (3 : ℕ) ≠ 0)] using
      mul_nonneg (by positivity : 0 ≤ K ^ 4) hD
  · have hpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
    have hp := pow_le_pow_left₀ hR hlower 4
    rw [mul_pow] at hp
    have hu := mul_le_mul_of_nonneg_left hfourth (by positivity : 0 ≤ K ^ 4)
    have hh : R * R ^ 3 ≤ R * (K ^ 4 * D) := by nlinarith
    exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [mul_comm R] using hh)

 theorem density_integral_alternative_count :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ T σ Y : ℝ,
      2 ≤ T → 1 / 2 < σ → 1 ≤ Y →
      ∀ {ι : Type} (S : Finset ι) (c : ι → PrimitiveComplexCharacter) (β t : ι → ℝ),
      (∀ i ∈ S, (c i).modulus ≤ Q) → (∀ i ∈ S, |t i| ≤ T) →
      (∀ i ∈ S, ∀ j ∈ S, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ S, σ ≤ β i ∧ β i ≤ 1 ∧ (c i).L (densityVerticalPoint (β i) (t i)) = 0) →
      (∀ i ∈ S, (1 / 8 : ℝ) ≤ ‖densityDetectorMean (c i) X (densityVerticalPoint (β i) (t i)) Y‖) →
      (S.card : ℝ) ^ 3 ≤ C * (128 * Y ^ (1 / 2 - σ) / (σ - 1 / 2)) ^ 4 *
        ((Q : ℝ) ^ 2 * T) * ((X : ℝ) + (Q : ℝ) ^ 2 * T) ^ 2 *
        (Real.log ((Q : ℝ) * T)) ^ 6 * (1 + Real.log X) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := density_packed_product_fourth
  refine ⟨C, hC, ?_⟩
  intro X Q hX hQ T σ Y hT hσ hY ι S c β t hc ht hsep hz hlarge
  let I0 := ∑ i ∈ S, densityCriticalMass (c i) X (t i)
  let K := 128 * Y ^ (1 / 2 - σ) / (σ - 1 / 2)
  let D := C * ((Q : ℝ) ^ 2 * T) * ((X : ℝ) + (Q : ℝ) ^ 2 * T) ^ 2 *
    (Real.log ((Q : ℝ) * T)) ^ 6 * (1 + Real.log X) ^ 2
  have hlower : (S.card : ℝ) ≤ K * I0 := by
    have hsum : (∑ _i ∈ S, (1 / 8 : ℝ)) ≤
        ∑ i ∈ S, (16 * Y ^ (1 / 2 - σ) / (σ - 1 / 2)) * densityCriticalMass (c i) X (t i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hlarge i hi).trans (densityDetector_uniform_mass_bound (c i) X σ (β i) (t i)
        hσ (hz i hi).1 (hz i hi).2.1 (hz i hi).2.2 Y hY)
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have hh := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 8)
    convert hh using 1
    · ring
    · dsimp [K, I0]
      ring
  have hfourth : I0 ^ 4 ≤ (S.card : ℝ) * D := by
    have h := hb X Q hX hQ T hT S c t hc ht hsep
    change I0 ^ 4 ≤ _ at h
    convert h using 1
    dsimp [D]
    ring
  have hmain := density_count_cube (S.card : ℝ) I0 K D (Nat.cast_nonneg _) (by dsimp [D]; positivity)
    hlower hfourth
  convert hmain using 1
  dsimp [K, D]
  ring

end Ostmann

end OAI
