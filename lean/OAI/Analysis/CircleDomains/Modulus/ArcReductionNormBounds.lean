import OAI.Analysis.CircleDomains.Topology.CompactArcReduction
import OAI.Analysis.CircleDomains.Selection.UncountableHitTail

namespace OAI

/-! The exact factor-two density and hit estimates yield the L² bounds
used in the compact-arc smallness statement. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem countingSquareNorm_twice {S : Type*} (m : S → ℝ≥0∞) :
    countingSquareNorm (fun s => 2 * m s) = 2 * countingSquareNorm m := by
  simp only [countingSquareNorm, mul_pow]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have htwo : ((2 : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) = 2 := by
    simpa only [Nat.cast_ofNat, one_div] using ENNReal.pow_rpow_inv_natCast (by decide : (2 : ℕ) ≠ 0) (2 : ℝ≥0∞)
  rw [htwo]

theorem arc_density_squareNorm_le
    {X : Type*} [MeasurableSpace X] (σ : Measure X)
    (g f : X → ℝ≥0∞) (hg : Measurable g) (W : Set X) (hW : MeasurableSet W)
    (hf : f ≤ᵐ[σ] fun x => 2 * W.indicator g x) :
    (∫⁻ x, f x ^ 2 ∂σ) ^ (1 / 2 : ℝ) ≤
      2 * (∫⁻ x in W, g x ^ 2 ∂σ) ^ (1 / 2 : ℝ) := by
  have hbound : (∫⁻ x, f x ^ 2 ∂σ) ≤ (2 : ℝ≥0∞) ^ 2 * ∫⁻ x in W, g x ^ 2 ∂σ := by
    calc
      _ ≤ ∫⁻ x, (2 * W.indicator g x) ^ 2 ∂σ :=
        lintegral_mono_ae (hf.mono fun x hx => pow_le_pow_left' hx 2)
      _ = _ := by
        have he : (fun x => (2 * W.indicator g x) ^ 2) =
            fun x => (2 : ℝ≥0∞) ^ 2 * W.indicator (fun x => g x ^ 2) x := by
          funext x
          by_cases hx : x ∈ W <;> simp [hx, mul_pow]
        rw [he, lintegral_const_mul _ ((hg.pow_const 2).indicator hW), lintegral_indicator hW]
  calc
    _ ≤ ((2 : ℝ≥0∞) ^ 2 * ∫⁻ x in W, g x ^ 2 ∂σ) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      have htwo : ((2 : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) = 2 := by
        simpa only [Nat.cast_ofNat, one_div] using ENNReal.pow_rpow_inv_natCast (by decide : (2 : ℕ) ≠ 0) (2 : ℝ≥0∞)
      rw [htwo]

theorem arc_hit_squareNorm_le {S : Type*} (m h : S → ℝ≥0∞) (p : S) (W : Set S)
    (hle : ∀ s, h s ≤ 2 * m s) (hout : ∀ s ∉ W, h s = 0) :
    countingSquareNorm (fun s => if s ≠ p then h s else 0) ≤
      2 * countingSquareNorm (fun s => if s ∈ W ∧ s ≠ p then m s else 0) := by
  calc
    _ ≤ countingSquareNorm (fun s => 2 * (if s ∈ W ∧ s ≠ p then m s else 0)) := by
      apply countingSquareNorm_mono
      intro s
      by_cases hp : s = p
      · simp [hp]
      · by_cases hs : s ∈ W
        · simpa only [hp, ne_eq, not_false_eq_true, hs, and_self, ite_true] using hle s
        · simp [hp, hs, hout s hs]
    _ = _ := countingSquareNorm_twice _

end CircleDomainRigidity

end

end OAI
