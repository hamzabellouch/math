import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.SupportCellRoot
import OAI.Analysis.RieszRectifiability.Foundations.NoncollapsingRegionRepresentatives
import OAI.Analysis.RieszRectifiability.Flatness.ContractedAffinePatch

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def cellProjectionNoncollapse {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (P : Submodule ℝ (Ambient d)) (κ : ℝ)
    (i : SupportCellDescendant μ R hR k z) : Prop :=
  ∀ v ∈ (S i).direction, κ * ‖v‖ ≤ ‖P.starProjection v‖

theorem cellProjectionNoncollapse_root {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (κ : ℝ) (hκ : κ ≤ 1) (i : SupportCellDescendant μ R hR k z) (hi : i.depth = 0) :
    cellProjectionNoncollapse S (S (supportCellRoot μ R hR k z)).direction κ i := by
  rw [i.eq_root_of_zero_depth hi]
  intro v hv
  rw [(S (supportCellRoot μ R hR k z)).direction.starProjection_eq_self_iff.mpr hv]
  simpa only [one_mul] using! mul_le_mul_of_nonneg_right hκ (norm_nonneg v)

theorem projection_conditioned_stop_contracted_unit {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (P : Submodule ℝ (Ambient d)) (κ : ℝ)
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z (cellProjectionNoncollapse S P κ)) :
    ∃ u : (S i).direction, ‖u‖ = 1 ∧ ‖P.starProjection (u : Ambient d)‖ < κ := by
  apply exists_contracted_unit_direction_of_not_lower (S i).direction P.starProjection.toLinearMap κ
  intro h
  apply hi.1
  intro v hv
  exact h ⟨v, hv⟩

end

end RieszRectifiability

end OAI
