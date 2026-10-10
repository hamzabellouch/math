import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.LocalAnnularFlatBall

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def HasFlatBallAbove {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (U : Set (Ambient d)) (ρ cap ε : ℝ) : Prop :=
  ∃ a ∈ μ.support, a ∈ U ∧ ∃ r : ℝ, 0 < r ∧ ρ ≤ r ∧ r < cap ∧ bilateralBeta n μ a r < ε

def HasLargeSmoothAnnulusAbove {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (U : Set (Ambient d)) (ρ cap B : ℝ) : Prop :=
  ∃ a ∈ μ.support, a ∈ U ∧ ∃ r R : ℝ, ∃ hr : 0 < r, ∃ hrR : r ≤ R,
    ρ ≤ r ∧ R < cap ∧ B < ‖smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)‖

theorem not_flat_ball_above_beta_lower {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (U : Set (Ambient d)) (ρ cap ε : ℝ) (hnot : ¬ HasFlatBallAbove n μ U ρ cap ε)
    (a : Ambient d) (ha : a ∈ μ.support) (haU : a ∈ U) (r : ℝ)
    (hr : 0 < r) (hρ : ρ ≤ r) (hcap : r < cap) : ε ≤ bilateralBeta n μ a r :=
  le_of_not_gt (fun h => hnot ⟨a, ha, haU, r, hr, hρ, hcap, h⟩)

theorem not_large_smooth_annulus_above_bound {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (U : Set (Ambient d)) (ρ cap B : ℝ) (hnot : ¬ HasLargeSmoothAnnulusAbove n μ U ρ cap B)
    (a : Ambient d) (ha : a ∈ μ.support) (haU : a ∈ U) (r R : ℝ)
    (hr : 0 < r) (hrR : r ≤ R) (hρ : ρ ≤ r) (hcap : R < cap) :
    ‖smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)‖ ≤ B :=
  le_of_not_gt (fun h => hnot ⟨a, ha, haU, r, R, hr, hrR, hρ, hcap, h⟩)

end

end RieszRectifiability

end OAI
