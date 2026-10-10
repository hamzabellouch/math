import OAI.NumberTheory.Ostmann.ZeroDensity.DensityActualBlock
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorBlocks
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorDyadicCover
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteBlockSquare

namespace OAI

/-! # Counting the polynomial alternative with its actual compact coefficients -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_polynomial_alternative_count :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ, 1 ≤ X → 1 ≤ Q → ∀ Y T σ : ℝ,
      2 ≤ Y → 1 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∀ i ∈ R, (1 / 8 : ℝ) ≤ ‖∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
        LSeries.term (densityDetectorCharacterCoefficient (c i) X) (densityVerticalPoint (β i) (t i)) n *
          densityDetectorWeight (n / Y)‖) →
      (R.card : ℝ) ≤ C * (1 + Real.log (2 * Y + 1)) ^ 9 *
        (Y ^ (2 - 2 * σ) + (Q : ℝ) ^ 2 * T * (X : ℝ) ^ (1 - 2 * σ)) := by
  obtain ⟨C, hC, hb⟩ := density_actual_block_bound
  let A := 2 / Real.log 2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨64 * C * A ^ 2, by positivity, ?_⟩
  intro X Q hX hQ Y T σ hY hT hσ hσ1 ι R c t β hc ht hs hβ hlarge
  obtain ⟨J, _hJ, hcover, hJbound⟩ := density_detector_dyadic_cover X hX Y hY
  let L := 1 + Real.log (2 * Y + 1)
  let G := Y ^ (2 - 2 * σ) + (Q : ℝ) ^ 2 * T * (X : ℝ) ^ (1 - 2 * σ)
  let f := fun i j => densityCharacterPolynomial (Finset.Ioc (2 ^ j * X) (2 * (2 ^ j * X)))
    (densityVerticalCoeff (densityPolynomialCoefficient X Y) (β i)) (c i).character (t i)
  have hL0 : 0 ≤ L := by
    have h := Real.log_nonneg (by linarith : 1 ≤ 2 * Y + 1)
    dsimp [L]
    linarith
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hblock (j : ℕ) : (∑ i ∈ R, ‖f i j‖ ^ 2) ≤ C * L ^ 7 * G := by
    apply hb X (2 ^ j * X) Q hX _ hQ Y T σ hY hT hσ hσ1 R c t β hc ht hs hβ
    exact Nat.le_mul_of_pos_left X (by positivity)
  have hlower : (R.card : ℝ) / 64 ≤ ∑ i ∈ R, ‖∑ j ∈ Finset.range J, f i j‖ ^ 2 := by
    have h := Finset.sum_le_sum (s := R) (fun i hi => show (1 / 64 : ℝ) ≤ ‖∑ j ∈ Finset.range J, f i j‖ ^ 2 from by
      have hh := hlarge i hi
      rw [densityDetector_polynomial_blocks (c i) X J hX Y (by linarith) hcover] at hh
      change (1 / 8 : ℝ) ≤ ‖∑ j ∈ Finset.range J, f i j‖ at hh
      nlinarith [norm_nonneg (∑ j ∈ Finset.range J, f i j)])
    simpa only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul] using h
  have hupper : (∑ i ∈ R, ‖∑ j ∈ Finset.range J, f i j‖ ^ 2) ≤
      (J : ℝ) ^ 2 * (C * L ^ 7 * G) := by
    apply (density_finite_block_square R J f).trans
    have h := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.range J) (fun j _ => hblock j))
      (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_two, mul_assoc] using h
  have hlog : Real.log Y ≤ L := by
    have h := Real.log_le_log (by linarith : 0 < Y) (by linarith : Y ≤ 2 * Y + 1)
    dsimp [L]
    linarith
  have hJ : (J : ℝ) ≤ A * L := hJbound.trans (mul_le_mul_of_nonneg_left hlog hA.le)
  have hJ2 := pow_le_pow_left₀ (Nat.cast_nonneg J : (0 : ℝ) ≤ J) hJ 2
  have hfinal := hlower.trans (hupper.trans (mul_le_mul_of_nonneg_right hJ2 (by positivity)))
  have hh := mul_le_mul_of_nonneg_left hfinal (by norm_num : (0 : ℝ) ≤ 64)
  convert hh using 1
  · ring
  · dsimp [L, G]
    ring

end Ostmann

end OAI
