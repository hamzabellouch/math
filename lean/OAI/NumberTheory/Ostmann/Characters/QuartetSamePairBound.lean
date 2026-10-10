import OAI.NumberTheory.Ostmann.Tree.SamePairHeldAverage
import OAI.NumberTheory.Ostmann.Characters.QuartetOrientedValue
import OAI.NumberTheory.Ostmann.Characters.QuartetRatioSwap

namespace OAI

/-! # Two moving leaves in the same bottom pair of an actual quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable def samePairLeftLeaves {U : Type*} [CommGroup U] (P a b r : U) :
    TreeLeafTuple U 2 := ((P / (a * r), r), (a / b, b))

theorem samePair_left_product {U : Type*} [CommGroup U] (P a r : U) :
    P / (a * r) * r = P / a := by
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

theorem samePair_total_product {U : Type*} [CommGroup U] (P a b r : U) :
    (P / (a * r) * r) * (a / b * b) = P := by
  rw [samePair_left_product, div_mul_cancel, div_mul_cancel]

noncomputable def samePairParentMultiplier {U : Type*} [CommGroup U]
    (Q : RationalQuartetData U) (XL XR P : U) : U :=
  (Q.sL / Q.sR) * (XR * Q.CR / (XL * Q.CL * P))

theorem samePair_parent_ratio {p : ℕ} [Fact p.Prime]
    (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a : (ZMod p)ˣ) :
    (Q.sL / Q.sR) * (XR * Q.CR * a / (XL * Q.CL * (P / a))) =
      samePairParentMultiplier Q XL XR P * a ^ 2 := by
  apply Units.ext
  simp only [samePairParentMultiplier, Units.val_mul, Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val]
  field_simp

/-- The held coordinates are the product and split of the right pair;
the second left leaf is the moving Mellin coordinate. -/
theorem samePairLeftLeaves_amplitude {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P a b r : (ZMod p)ˣ) :
    rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true))
      (samePairLeftLeaves P a b r) =
    quartetRatioValue g g true true
      (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
      (quartetLeftHeld D Q XL * r ^ 2) (quartetRightHeld D Q XR * b ^ 2)
      (samePairParentMultiplier Q XL XR P * a ^ 2) := by
  change rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true))
    ((P / (a * r), r), (a / b, b)) = _
  rw [rationalTreeAmplitude_quartet, rationalQuartetValue_oriented g D Q _ _ _ _ _ _ true true]
  rw [samePair_total_product, samePair_left_product, div_mul_cancel, samePair_parent_ratio]
  rfl

theorem rationalQuartet_samePair_left_held_bound {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true))
            (samePairLeftLeaves P a b r)) ρ‖ ^ 2) ≤
      8 * samePairMajorant (fieldPairCoefficientMoment g) (fieldPairMoment g) ρ
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  simp_rw [samePairLeftLeaves_amplitude]
  exact samePair_held_coefficient_le g g _ _ _ _ ρ

noncomputable def samePairRightLeaves {U : Type*} [CommGroup U] (P a b r : U) :
    TreeLeafTuple U 2 := ((a⁻¹ / b, b), (P * a / r, r))

theorem samePair_right_total_product {U : Type*} [CommGroup U] (P a b r : U) :
    (a⁻¹ / b * b) * (P * a / r * r) = P := by
  rw [div_mul_cancel, div_mul_cancel]
  simp [mul_comm]

noncomputable def samePairRightParentMultiplier {U : Type*} [CommGroup U]
    (Q : RationalQuartetData U) (XL XR P : U) : U :=
  (Q.sL / Q.sR) * (XR * Q.CR * P / (XL * Q.CL))

theorem samePair_right_parent_ratio {p : ℕ} [Fact p.Prime]
    (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P a : (ZMod p)ˣ) :
    (Q.sL / Q.sR) * (XR * Q.CR * (P * a) / (XL * Q.CL * a⁻¹)) =
      samePairRightParentMultiplier Q XL XR P * a ^ 2 := by
  apply Units.ext
  simp only [samePairRightParentMultiplier, Units.val_mul, Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  field_simp

theorem samePairRightLeaves_amplitude {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P a b r : (ZMod p)ˣ) :
    rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true))
      (samePairRightLeaves P a b r) =
    quartetRatioValue g g true true
      (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
      (quartetLeftHeld D Q XL * b ^ 2) (quartetRightHeld D Q XR * r ^ 2)
      (samePairRightParentMultiplier Q XL XR P * a ^ 2) := by
  change rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true))
    ((a⁻¹ / b, b), (P * a / r, r)) = _
  rw [rationalTreeAmplitude_quartet, rationalQuartetValue_oriented g D Q _ _ _ _ _ _ true true]
  rw [samePair_right_total_product, div_mul_cancel, div_mul_cancel, samePair_right_parent_ratio]
  rfl

theorem rationalQuartet_samePair_right_held_bound {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true))
            (samePairRightLeaves P a b r)) ρ‖ ^ 2) ≤
      8 * samePairMajorant (fieldPairCoefficientMoment g) (fieldPairMoment g) ρ
        (-rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  simp_rw [samePairRightLeaves_amplitude]
  exact samePair_right_held_coefficient_le g g _ _ _ _ ρ

end Ostmann

end OAI
