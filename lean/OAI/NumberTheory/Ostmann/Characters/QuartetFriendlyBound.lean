import OAI.NumberTheory.Ostmann.Characters.QuartetFriendlyCoordinates

namespace OAI

/-! # The local coefficient estimate on actual friendly quartets -/

namespace Ostmann

open scoped BigOperators

/-- The held-leaf coefficient bound applied to the actual recursive diagram,
with no hypothesis asserting an unidentified local quartet estimate. -/
theorem rationalQuartet_friendly_held_bound {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun (r : (ZMod p)ˣ) => rationalTreeAmplitude g D Q.tree XL XR
          ((false, true), (false, true))
          (((r⁻¹ : (ZMod p)ˣ), a), ((P * r / (a * b) : (ZMod p)ˣ), b))) ρ‖ ^ 2) ≤
      8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        crossPairMajorant g g true true ρ⁻¹
          (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  simp_rw [rationalTreeAmplitude_quartet, rationalQuartetValue_friendly]
  exact crossPair_held_coefficient_le g g true true
    (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
    (quartetLeftHeld D Q XL) (quartetRightHeld D Q XR)
    (fun a _b => quartetMovingMultiplier Q XL XR P a) ρ

end Ostmann

end OAI
