import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalPairingEnergy
import OAI.Analysis.RieszRectifiability.Kernel.UniformHeightTail

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

def normalizedEnergyCoefficient (p : ℕ) (C M H R A J : ℝ) (L : ℝ≥0) : ℝ :=
  2 * (A + 2 ^ (p + 1 + 1) * (M * (2 * (C * 2 ^ (p + 1) / R))) +
    ((p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2) * H) * (M * J)) +
    localCutoffErrorCoefficient p C L R * M

theorem fractionalPairEnergy_div {X : Type*} [MetricSpace X]
    (m : ℕ) (f : X → ℝ) (δ : ℝ) (x y : X) :
    fractionalPairEnergy m (fun z => f z / δ) x y = fractionalPairEnergy m f x y / δ ^ 2 := by
  unfold fractionalPairEnergy
  rw [← sub_div, div_pow]
  ring

theorem normalizedEnergyCoefficient_nonneg (p : ℕ) (C M H R A J : ℝ) (L : ℝ≥0)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hH : 0 ≤ H) (hR : 0 < R) (hA : 0 ≤ A) (hJ : 0 ≤ J) :
    0 ≤ normalizedEnergyCoefficient p C M H R A J L := by
  unfold normalizedEnergyCoefficient localCutoffErrorCoefficient
  positivity

theorem normalized_cutoff_energy_bound {d : ℕ} (p : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hCB : C * 2 ^ (p + 1) ≤ B)
    (w χ : Ambient d → ℝ) (K L : ℝ≥0) (hw : LipschitzWith K w) (hχ : LipschitzWith L χ)
    (hχbound : ∀ x, |χ x| ≤ 1) (a : Ambient d) (H R : ℝ)
    (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (M δ b W A : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hW : |w a| ≤ W) (hA : 0 ≤ A) (N : ℕ) (hlast : (R * 2 ^ N)⁻¹ ≤ δ)
    (hmass : C * R ^ (p + 1) ≤ M)
    (hsecond : (∫ x in ball a R, w x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hshell : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ (p + 1)) * (δ * (R * 2 ^ k) * b ^ k) ^ 2)
    (hsmall : |normalCutoffPairing (p + 1) μ a R w χ| ≤ A * δ ^ 2) :
    0 ≤ normalizedEnergyCoefficient p C M H R A (heightTailLinearCoefficient (p + 1) C B R b K W) L ∧
      Integrable (fun q : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => (χ x * w x) / δ) q.1 q.2)
        ((μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => (χ x * w x) / δ) q.1 q.2
          ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ≤
        normalizedEnergyCoefficient p C M H R A (heightTailLinearCoefficient (p + 1) C B R b K W) L := by
  let J := heightTailLinearCoefficient (p + 1) C B R b K W
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hJ : 0 ≤ J := heightTailLinearCoefficient_nonneg (p + 1) C B R b K W
    hg.1 hB hR hb2 ((abs_nonneg _).trans hW)
  obtain ⟨hweighted, hZ⟩ := weighted_height_tail_linear_bound (p + 1) C B μ hg hCB w K hw
    a R hR N δ b W hδ.le hb0 hb2 hW hlast hshell
  obtain ⟨hE, hEnergyBound⟩ := normalCutoffPairing_energy_bound p C μ hg w χ K L hw hχ hχbound
    a H R hH hR hHR hχsupport M δ hM hδ.le hmass hsecond hweighted (J * δ) hZ (A * δ ^ 2) hsmall
  have hUnscaled : (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ≤
      normalizedEnergyCoefficient p C M H R A J L * δ ^ 2 := by
    convert! hEnergyBound using 1
    unfold normalExteriorEstimate normalizedEnergyCoefficient
    push_cast
    ring
  refine ⟨normalizedEnergyCoefficient_nonneg p C M H R A J L hg.1 hM hH hR hA hJ, ?_, ?_⟩
  · simpa only [fractionalPairEnergy_div] using! hE.div_const (δ ^ 2)
  · simp_rw [fractionalPairEnergy_div]
    rw [integral_div]
    exact (div_le_iff₀ (sq_pos_of_pos hδ)).mpr hUnscaled

end

end RieszRectifiability

end OAI
