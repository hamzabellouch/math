import OAI.Geometry.RCD.Heat.HeatControls
import OAI.Geometry.RCD.Coordinates.BilinearHeatEnvelope

namespace OAI

/-! # Pointwise envelope order after the finite initial scales -/

open scoped BigOperators InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual eventual heat controls also give order of the mass
envelope by the current metric, with the finite background kept explicit. -/
theorem EventualHeatControls.envelope_le_current
    {Q : ℕ → E ≃L[ℝ] E} {N F : ℕ → E →L[ℝ] E} {J : ℕ} {ε C b T : ℝ}
    (h : EventualHeatControls Q N F J ε C)
    (hQ : ∀ i, (Q i : E →L[ℝ] E).IsPositive)
    (hε : 0 ≤ ε) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (hbase : ∀ v, ‖v‖ ^ 2 ≤ T * ⟪v, Q J v⟫_ℝ)
    (hbackground : ∀ i v, ⟪v, F (J + i) v⟫_ℝ ≤ b * (3 / 4 : ℝ) ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), (3 / 4 : ℝ) ^ (i - j) * ⟪v, N (J + j) v⟫_ℝ)
    (i : ℕ) (v : E) :
    ⟪v, F (J + i) v⟫_ℝ ≤ (b * T + 8 * ε) * ⟪v, Q (J + i) v⟫_ℝ := by
  apply heat_envelope_le_current (fun j => (Q (J + j) : E →L[ℝ] E))
    (fun j => N (J + j)) (fun j => F (J + j)) (fun j => hQ (J + j)) hb hT hε
    (fun j w => by simpa only [Nat.add_assoc, ContinuousLinearEquiv.coe_coe] using h.step (J + j) (Nat.le_add_right J j) w)
    (by simpa only [Nat.add_zero, ContinuousLinearEquiv.coe_coe] using hbase)
    (fun j w => h.small (J + j) (Nat.le_add_right J j) w)
    hbackground i v

end RegularPointCoordinates

end

end OAI
