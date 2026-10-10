import OAI.NumberTheory.CubicMoment.Decomposition.StoppingBinShift
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingLogBoundary

namespace OAI

/-! An active logarithmic boundary for a larger ambient envelope, with
roughness still measured in the original parameter X. The index shift is
chosen explicitly, so no comparison of logarithms of two scales is needed. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma geometric_boundary_shift {ρ X F : ℝ} (hρ : 1 < ρ)
    (hX : 0 < X) (hXF : X ≤ F) {h : ℕ} (hh : h < geometricBinCount ρ X) :
    h+(geometricBinCount ρ F-geometricBinCount ρ X) < geometricBinCount ρ F ∧
      geometricBinLower ρ F (h+(geometricBinCount ρ F-geometricBinCount ρ X)) =
        geometricBinLower ρ X h := by
  have hc := geometricBinCount_mono hρ hX hXF
  exact ⟨by omega,geometricBinLower_shift hρ hX hXF h⟩

theorem eventually_stopping_active_boundary_envelope {ξ : ℝ}
    (hξ : 0 < ξ) (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ F : ℝ, X ≤ F → ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∃ h : ℕ, h < geometricBinCount ρ F ∧
        geometricBinCount ρ F-geometricBinCount ρ X ≤ h ∧
        2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower ρ F h) ∧
        ρ*geometricBinLower ρ F h ≤ (Real.log X)^(G+4) := by
  filter_upwards [eventually_stopping_active_boundary hξ G,
    eventually_gt_atTop (0:ℝ)] with X hbound hX
  intro F hXF ρ hρ hρ₂
  obtain ⟨h,hh,hlo,hhi⟩ := hbound (ρ-1) (by linarith) (by linarith)
  have hr : 1+(ρ-1) = ρ := by ring
  rw [hr] at hh hlo hhi
  have hc := geometricBinCount_mono hρ hX hXF
  refine ⟨h+(geometricBinCount ρ F-geometricBinCount ρ X),by omega,by omega,?_,?_⟩
  · simpa only [geometricBinLower_shift hρ hX hXF] using hlo
  · simpa only [geometricBinLower_shift hρ hX hXF] using hhi

end CubicFirstMoment

end

end OAI
