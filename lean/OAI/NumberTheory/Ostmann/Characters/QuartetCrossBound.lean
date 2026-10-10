import OAI.NumberTheory.Ostmann.Characters.QuartetOrientedValue

namespace OAI

/-! # The coefficient bound for every cross-pair orientation of an actual quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable def crossLeftLeaves {U : Type*} [CommGroup U]
    (friendly : Bool) (a r : U) : U × U := if friendly then (r⁻¹, a) else (a, r⁻¹)

noncomputable def crossRightLeaves {U : Type*} [CommGroup U]
    (friendly : Bool) (P a b r : U) : U × U :=
  if friendly then (P * r / (a * b), b) else (b, P * r / (a * b))

noncomputable def crossQuartetLeaves {U : Type*} [CommGroup U]
    (left right : Bool) (P a b r : U) : TreeLeafTuple U 2 :=
  ((crossLeftLeaves left a r : U × U), (crossRightLeaves right P a b r : U × U))

theorem crossLeftLeaves_product {U : Type*} [CommGroup U]
    (friendly : Bool) (a r : U) :
    (crossLeftLeaves friendly a r).1 * (crossLeftLeaves friendly a r).2 = r⁻¹ * a := by
  cases friendly <;> simp [crossLeftLeaves, mul_comm]

theorem crossRightLeaves_product {U : Type*} [CommGroup U]
    (friendly : Bool) (P a b r : U) :
    (crossRightLeaves friendly P a b r).1 * (crossRightLeaves friendly P a b r).2 =
      P * r / (a * b) * b := by
  cases friendly <;> simp [crossRightLeaves, mul_comm]

theorem crossLeftLeaves_parameter {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a r : (ZMod p)ˣ)
    (friendly : Bool) :
    quartetLeftParameter D Q XL XR P friendly
      (crossLeftLeaves friendly a r).1 (crossLeftLeaves friendly a r).2 =
      (if friendly then quartetLeftHeld D Q XL else quartetLeftBadHeld D Q XL XR P) * a ^ 2 := by
  cases friendly <;> rfl

theorem crossRightLeaves_parameter {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a b r : (ZMod p)ˣ)
    (friendly : Bool) :
    quartetRightParameter D Q XL XR P friendly
      (crossRightLeaves friendly P a b r).1 (crossRightLeaves friendly P a b r).2 =
      (if friendly then quartetRightHeld D Q XR else quartetRightBadHeld D Q XL XR P) * b ^ 2 := by
  cases friendly <;> rfl

/-- The product-fiber coordinates preserve both held leaves and expose the
same inverse-square moving ratio for all four orientations. -/
theorem crossQuartetLeaves_amplitude {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P a b r : (ZMod p)ˣ) (left right : Bool) :
    rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true))
      (crossQuartetLeaves left right P a b r) =
    quartetRatioValue (orientedPairBase g left) (orientedPairBase g right) left right
      (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
      ((if left then quartetLeftHeld D Q XL else quartetLeftBadHeld D Q XL XR P) * a ^ 2)
      ((if right then quartetRightHeld D Q XR else quartetRightBadHeld D Q XL XR P) * b ^ 2)
      (quartetMovingMultiplier Q XL XR P a * r ^ 2) := by
  change rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true))
    (((crossLeftLeaves left a r).1, (crossLeftLeaves left a r).2),
      ((crossRightLeaves right P a b r).1, (crossRightLeaves right P a b r).2)) = _
  rw [rationalTreeAmplitude_quartet, rationalQuartetValue_oriented]
  rw [crossLeftLeaves_product, crossRightLeaves_product, quartet_friendly_product]
  rw [crossLeftLeaves_parameter, crossRightLeaves_parameter]
  rw [quartet_friendly_ratio]

/-- Every choice of one moving leaf in each pair has the already proved
square-pullback majorant, directly on the actual recursive tree amplitude. -/
theorem rationalQuartet_cross_held_bound {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (left right : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun (r : (ZMod p)ˣ) =>
          rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true))
            (crossQuartetLeaves left right P a b r)) ρ‖ ^ 2) ≤
    8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
      crossPairMajorant (orientedPairBase g left) (orientedPairBase g right) left right ρ⁻¹
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  simp_rw [crossQuartetLeaves_amplitude]
  exact crossPair_held_coefficient_le _ _ left right _ _ _
    (fun a _b => quartetMovingMultiplier Q XL XR P a) ρ

end Ostmann

end OAI
