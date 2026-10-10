import Mathlib.Analysis.Complex.ExponentialBounds
import OAI.NumberTheory.Ostmann.ZeroDensity.LowHeightZeroExclusion

namespace OAI

/-! # The actual low-height real-character zero-free region -/

namespace Ostmann

open Complex
open scoped Classical

/-- A single absolute zero-free constant works for every real primitive
character. Shrinking the progression constant will align the two inputs. -/
theorem exists_actual_real_low_height_region : ∃ κ : ℝ, 0 < κ ∧
    ∀ P : PublishedProgressionInput, P.kappa ≤ κ → ActualRealLowHeightRegion P := by
  obtain ⟨R, hR, hreal⟩ := exists_real_zero_sum_upper
  obtain ⟨S, hS, hshift⟩ := exists_low_height_shifted_bound
  let D : ℝ := R + S + 4
  have hD : 0 < D := by dsimp [D]; positivity
  let κ : ℝ := 1 / (2000 * D)
  refine ⟨κ, by dsimp [κ]; positivity, ?_⟩
  intro P hP χ Q hQ hq
  let H : ℝ := Real.log (4 * (Q : ℝ))
  have hQr : 2 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hH : 1 ≤ H := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < 4 * (Q : ℝ))).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hHpos : 0 < H := by linarith
  have hlog : Real.log χ.modulus ≤ H := by
    apply Real.log_le_log (by exact_mod_cast χ.positive)
    have hh : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hq
    linarith
  let δ : ℝ := 1 / (100 * D * H)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_one (by positivity : 0 < 100 * D * H)).mpr
    have hh := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ D)
    dsimp [D] at *
    nlinarith
  have hRerr : δ * ((1 / 2) * Real.log χ.modulus + R) ≤ 1 / 10 := by
    rw [show δ * ((1 / 2) * Real.log χ.modulus + R) =
      ((1 / 2) * Real.log χ.modulus + R) / (100 * D * H) by dsimp [δ]; ring]
    apply (div_le_iff₀ (by positivity : 0 < 100 * D * H)).mpr
    have hrh := mul_le_mul_of_nonneg_left hH hR.le
    have hsh := mul_nonneg hS.le hHpos.le
    dsimp [D]
    nlinarith
  have hSerr : δ * (2 * Real.log χ.modulus + S) ≤ 1 / 10 := by
    rw [show δ * (2 * Real.log χ.modulus + S) =
      (2 * Real.log χ.modulus + S) / (100 * D * H) by dsimp [δ]; ring]
    apply (div_le_iff₀ (by positivity : 0 < 100 * D * H)).mpr
    have hsh := mul_le_mul_of_nonneg_left hH hS.le
    have hrh := mul_nonneg hR.le hHpos.le
    dsimp [D]
    nlinarith
  have hr : shiftedRealCharacterZeroSum χ ((1 + δ : ℝ) : ℂ) ≤
      1 / δ + ((1 / 2) * Real.log χ.modulus + R) := by
    simpa only [add_sub_cancel_left, add_assoc] using
      hreal χ (1 + δ) (by linarith) (by linarith)
  have hs : ∀ t : ℝ, |t| ≤ 1 →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + 2 * Real.log χ.modulus + S := by
    intro t ht
    simpa only [add_sub_cancel_left] using
      hshift χ (1 + δ) t (by linarith) (by linarith) ht
  obtain ⟨hrealzero, huniq⟩ := near_low_height_zeros_real_unique χ δ
    ((1 / 2) * Real.log χ.modulus + R) S hδ hδ1 hRerr hSerr hr hs
  have hgap : P.kappa / H ≤ δ / 20 := by
    apply (div_le_div_of_nonneg_right hP hHpos.le).trans
    have he : κ / H = δ / 20 := by
      dsimp [κ, δ]
      field_simp
      ring
    exact he.le
  let E := ((realCharacterActualZeros χ).heightIndices 1).filter
    (fun i => 1 - P.kappa / H < ((realCharacterActualZeros χ).zeros i).re)
  have hmem (i : ℕ) : i ∈ E ↔ |((realCharacterActualZeros χ).zeros i).im| ≤ 1 ∧
      1 - P.kappa / H < ((realCharacterActualZeros χ).zeros i).re := by
    simp [E]
  refine ⟨E, Finset.card_le_one.mpr ?_, ?_, ?_⟩
  · intro i hi j hj
    have hi' := (hmem i).mp hi
    have hj' := (hmem j).mp hj
    exact huniq i j (by linarith [hi'.2]) (by linarith [hj'.2]) hi'.1 hj'.1
  · intro i hi
    have hi' := (hmem i).mp hi
    exact ⟨hrealzero i (by linarith [hi'.2]) hi'.1, hi'.2.le⟩
  · intro i hi him
    by_contra hb
    have him' : |((realCharacterActualZeros χ).zeros i).im| ≤ 1 := by
      nlinarith [sq_abs ((realCharacterActualZeros χ).zeros i).im,
        abs_nonneg ((realCharacterActualZeros χ).zeros i).im]
    exact hi ((hmem i).mpr ⟨him', lt_of_not_ge hb⟩)

end Ostmann

end OAI
