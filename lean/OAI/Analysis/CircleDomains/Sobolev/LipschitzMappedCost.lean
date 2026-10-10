import OAI.Analysis.CircleDomains.Sobolev.LipschitzMappedArclength

namespace OAI

/-! Weighted physical cost under a Lipschitz change of ambient metric. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem lipschitzMappedPath_cost_le (α : RectifiablePath X) (f : X → Y)
    {S : Set X} {L : ℝ≥0} (hL : LipschitzOnWith L f S) (hα : ∀t, α.val t ∈ S)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y, g y ∂pathOccupation (lipschitzMappedPath α f hL hα)) ≤
      (L : ℝ≥0∞) * ∫⁻t, g (f (α.val t)) ∂pathLengthMeasure α := by
  rw [lintegral_pathOccupation _ hg]
  calc
    _ ≤ ∫⁻t, g (f (α.val t)) ∂(L • pathLengthMeasure α) :=
      lintegral_mono' (lipschitzMappedPath_length_le α f hL hα) (fun _ => le_rfl)
    _ = _ := by rw [lintegral_smul_measure]; rfl

theorem lipschitzMappedPath_cost_lt_top (α : RectifiablePath X) (f : X → Y)
    {S : Set X} {L : ℝ≥0} (hL : LipschitzOnWith L f S) (hα : ∀t, α.val t ∈ S)
    (g : Y → ℝ≥0∞) (hg : Measurable g)
    (hfinite : (∫⁻t, g (f (α.val t)) ∂pathLengthMeasure α) < ∞) :
    (∫⁻y, g y ∂pathOccupation (lipschitzMappedPath α f hL hα)) < ∞ :=
  (lipschitzMappedPath_cost_le α f hL hα g hg).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hfinite)

end CircleDomainRigidity

end

end OAI
