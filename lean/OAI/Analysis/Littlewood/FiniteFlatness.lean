import OAI.Analysis.Littlewood.MinimizingFamily
import OAI.MeasureTheory.Integral.BoundedMoments
import OAI.Analysis.Littlewood.Main

namespace OAI

/-! Finite positive real power-moment flatness for one all-length real-sign family. -/
namespace AsymptoticallyMinimalLittlewoodFiniteFlatness

open MeasureTheory
open scoped BigOperators Topology

/-- One all-length real-sign family, simultaneously for every finite positive real exponent. -/
theorem main : MainStatement := by
  have hmain : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N := by
    change AsymptoticallyMinimalLittlewood.MainStatement
    exact AsymptoticallyMinimalLittlewood.main
  refine ⟨chosenSigns, chosenSigns_signing, ?_⟩
  intro p hp
  have h := LittlewoodFiniteFlatness.tendsto_integral_abs_sub_one_rpow
    μ normalized normalized_measurable normalized_nonneg
    (normalized_eventually_le_two hmain) (normalized_error_sq_tendsto hmain) p hp
  simpa only [normalized, circlePolynomial_apply, μ, Real.rpow_eq_pow] using h

end AsymptoticallyMinimalLittlewoodFiniteFlatness

end OAI
