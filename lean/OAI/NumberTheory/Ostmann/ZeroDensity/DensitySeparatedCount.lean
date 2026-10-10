import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPolynomialBalanced
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityIntegralBalanced

namespace OAI

/-! # Combining the two genuine detector alternatives at separated zeros -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_four_to_nine_logs (L : ℝ) (hL : Real.log 2 ≤ L) :
    L ^ 4 ≤ (Real.log 2)⁻¹ ^ 5 * L ^ 9 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := pow_le_pow_left₀ hl.le hL 5
  calc
    L ^ 4 = (Real.log 2)⁻¹ ^ 5 * ((Real.log 2) ^ 5 * L ^ 4) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl.ne', one_pow, one_mul]
    _ ≤ (Real.log 2)⁻¹ ^ 5 * (L ^ 5 * L ^ 4) := by gcongr
    _ = _ := by ring

 theorem density_separated_zero_count :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ,
      2 ≤ T → 4 ≤ (Q : ℝ) ^ 2 * T → 1 / 2 < σ → σ ≤ 1 →
      1 / Real.log ((Q : ℝ) ^ 2 * T) ≤ σ - 1 / 2 →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1 ∧ (c i).L (densityVerticalPoint (β i) (t i)) = 0) →
      (R.card : ℝ) ≤ C * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
        (Real.log ((Q : ℝ) * T)) ^ 9 := by
  obtain ⟨C1, hC1, hp⟩ := density_polynomial_alternative_balanced
  obtain ⟨C2, hC2, hi⟩ := density_integral_alternative_balanced
  refine ⟨C1 + (C2 + 1) * (Real.log 2)⁻¹ ^ 5, by positivity, ?_⟩
  intro Q hQ T σ hT hB4 hσ hσ1 hgap ι R c t β hc ht hs hz
  obtain ⟨X, hX, hBX, hiX⟩ := hi Q hQ T σ hT hσ hσ1 hgap
  let B := (Q : ℝ) ^ 2 * T
  let Y := B ^ densityBalanceExponent σ
  let L := Real.log ((Q : ℝ) * T)
  let p : ι → Prop := fun i => (1 / 8 : ℝ) ≤ ‖∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
    LSeries.term (densityDetectorCharacterCoefficient (c i) X) (densityVerticalPoint (β i) (t i)) n *
      densityDetectorWeight (n / Y)‖
  let P := R.filter p
  let N := R.filter (fun i => ¬p i)
  have hY : 4 ≤ Y := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ B)
      (density_balance_at_least_one σ hσ.le hσ1)
    rw [Real.rpow_one] at hh
    exact hB4.trans hh
  have hP := hp Q hQ T σ hT hσ.le hσ1 X hX hBX P c t β
    (fun i h => hc i (Finset.mem_filter.mp h).1)
    (fun i h => ht i (Finset.mem_filter.mp h).1)
    (fun i h j h' => hs i (Finset.mem_filter.mp h).1 j (Finset.mem_filter.mp h').1)
    (fun i h => ⟨(hz i (Finset.mem_filter.mp h).1).1, (hz i (Finset.mem_filter.mp h).1).2.1⟩)
    (fun _ h => (Finset.mem_filter.mp h).2)
  have hNlarge (i : ι) (hiN : i ∈ N) :
      (1 / 8 : ℝ) ≤ ‖densityDetectorMean (c i) X (densityVerticalPoint (β i) (t i)) Y‖ := by
    obtain ⟨hir, hn⟩ := Finset.mem_filter.mp hiN
    have hzi := hz i hir
    have hd := densityDetector_dichotomy (c i) X hX (densityVerticalPoint (β i) (t i))
      (by simpa [densityVerticalPoint] using hσ.trans_le hzi.1)
      (by simpa [densityVerticalPoint] using hzi.2.1) hzi.2.2 Y hY
    rcases hd with h | h
    · exact False.elim (hn h)
    · rw [densityDetectorMean_at_zero (c i) X _
        (by simpa [densityVerticalPoint] using hσ.trans_le hzi.1)
        (by simpa [densityVerticalPoint] using hzi.2.1) hzi.2.2 Y (by linarith)]
      exact h
  have hNcube := hiX N c β t
    (fun i h => hc i (Finset.mem_filter.mp h).1)
    (fun i h => ht i (Finset.mem_filter.mp h).1)
    (fun i h j h' => hs i (Finset.mem_filter.mp h).1 j (Finset.mem_filter.mp h').1)
    (fun i h => hz i (Finset.mem_filter.mp h).1) hNlarge
  have hN := density_balanced_count_from_cube C2 N.card B σ L hC2.le (Nat.cast_nonneg _)
    (by dsimp [B]; positivity) hNcube
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hN' : (N.card : ℝ) ≤ (C2 + 1) * B ^ densityTargetExponent σ *
      ((Real.log 2)⁻¹ ^ 5 * L ^ 9) :=
    hN.trans (mul_le_mul_of_nonneg_left (density_four_to_nine_logs L hL) (by positivity))
  have hcard : (R.card : ℝ) = (P.card : ℝ) + (N.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := R) (p := p)).symm
  rw [hcard]
  have hh := add_le_add hP hN'
  convert hh using 1
  dsimp [B, L]
  ring

end Ostmann

end OAI
