import OAI.Analysis.CircleDomains.Sobolev.LipschitzArclengthBounds
import OAI.Analysis.CircleDomains.Probability.PathOccupation

namespace OAI

/-! Finite weighted Hausdorff length pays for an actual embedded path
whenever the chosen parameter is Lipschitz in both directions. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem bilipschitz_pathOccupation_le (γ : RectifiablePath X) {L K : ℝ≥0}
    (hL : LipschitzWith L γ.val) (hL0 : L ≠ 0)
    (hK : AntilipschitzWith K γ.val) :
    pathOccupation γ ≤ ((L : ℝ≥0∞) * K) •
      (μH[1] : Measure X).restrict (range γ.val) := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [pathOccupation_apply γ hs]
  have he : γ.val ⁻¹' s = γ.val ⁻¹' (s ∩ range γ.val) := by
    ext t
    simp only [mem_preimage, mem_inter_iff]
    exact ⟨fun h => ⟨h, mem_range_self t⟩, And.left⟩
  calc
    pathLengthMeasure γ (γ.val ⁻¹' s) ≤
        (L : ℝ≥0∞) * (μH[1] : Measure PathTime) (γ.val ⁻¹' s) :=
      lipschitz_pathLength_le_hausdorff γ hL hL0 _
    _ = (L : ℝ≥0∞) * (μH[1] : Measure PathTime)
        (γ.val ⁻¹' (s ∩ range γ.val)) := by rw [he]
    _ ≤ (L : ℝ≥0∞) * ((K : ℝ≥0∞) * (μH[1] : Measure X) (s ∩ range γ.val)) := by
      apply mul_le_mul' le_rfl
      simpa only [ENNReal.rpow_one] using
        hK.hausdorffMeasure_preimage_le (show (0 : ℝ) ≤ 1 by norm_num) (s ∩ range γ.val)
    _ = _ := by rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs, mul_assoc]

theorem bilipschitz_pathCost_lt_top (γ : RectifiablePath X) {L K : ℝ≥0}
    (hL : LipschitzWith L γ.val) (hL0 : L ≠ 0)
    (hK : AntilipschitzWith K γ.val) (g : X → ℝ≥0∞)
    (hfinite : (∫⁻ x in range γ.val, g x ∂(μH[1] : Measure X)) < ∞) :
    (∫⁻ x, g x ∂pathOccupation γ) < ∞ := by
  calc
    (∫⁻ x, g x ∂pathOccupation γ) ≤
        ∫⁻ x, g x ∂(((L : ℝ≥0∞) * K) •
          (μH[1] : Measure X).restrict (range γ.val)) :=
      lintegral_mono' (bilipschitz_pathOccupation_le γ hL hL0 hK) (fun _ => le_rfl)
    _ = ((L : ℝ≥0∞) * K) *
        ∫⁻ x in range γ.val, g x ∂(μH[1] : Measure X) := lintegral_smul_measure _ _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top) hfinite

end CircleDomainRigidity

end

end OAI
