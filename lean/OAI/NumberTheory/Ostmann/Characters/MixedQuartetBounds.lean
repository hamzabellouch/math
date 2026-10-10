import OAI.NumberTheory.Ostmann.Characters.MixedQuartetCoordinates
import OAI.NumberTheory.Ostmann.Characters.QuartetSamePairBound
import OAI.NumberTheory.Ostmann.Characters.QuartetCrossBound
import OAI.NumberTheory.Ostmann.Tree.UntouchedQuartetBound

namespace OAI

/-! # Local bounds for every opposite sibling conjugation choice -/

namespace Ostmann

open scoped BigOperators

theorem crossQuartetLeaves_amplitude_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P a b r : (ZMod p)ˣ) (cL cR left right : Bool) :
    rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
      (crossQuartetLeaves left right P a b r) =
    quartetRatioValue (orientedPairBase (pairConjugate g cL) left)
      (orientedPairBase (pairConjugate g cR) right) left right
      (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
      ((if left then quartetLeftHeld D Q XL else quartetLeftBadHeld D Q XL XR P) * a ^ 2)
      ((if right then quartetRightHeld D Q XR else quartetRightBadHeld D Q XL XR P) * b ^ 2)
      (quartetMovingMultiplier Q XL XR P a * r ^ 2) := by
  change rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
    (((crossLeftLeaves left a r).1, (crossLeftLeaves left a r).2),
      ((crossRightLeaves right P a b r).1, (crossRightLeaves right P a b r).2)) = _
  rw [rationalTreeAmplitude_quartet_conjugation, rationalQuartetPairsValue_oriented]
  rw [crossLeftLeaves_product, crossRightLeaves_product, quartet_friendly_product]
  rw [crossLeftLeaves_parameter, crossRightLeaves_parameter, quartet_friendly_ratio]

theorem rationalQuartet_cross_held_bound_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (cL cR left right : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
            (crossQuartetLeaves left right P a b r)) ρ‖ ^ 2) ≤
    8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
      crossPairMajorant (orientedPairBase (pairConjugate g cL) left)
        (orientedPairBase (pairConjugate g cR) right) left right ρ⁻¹
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  simp_rw [crossQuartetLeaves_amplitude_conjugation]
  exact crossPair_held_coefficient_le _ _ left right _ _ _
    (fun a _b => quartetMovingMultiplier Q XL XR P a) ρ

theorem samePairLeftLeaves_amplitude_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P a b r : (ZMod p)ˣ) (cL cR : Bool) :
    rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
      (samePairLeftLeaves P a b r) =
    quartetRatioValue (pairConjugate g cL) (pairConjugate g cR) true true
      (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
      (quartetLeftHeld D Q XL * r ^ 2) (quartetRightHeld D Q XR * b ^ 2)
      (samePairParentMultiplier Q XL XR P * a ^ 2) := by
  change rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
    ((P / (a * r), r), (a / b, b)) = _
  rw [rationalTreeAmplitude_quartet_conjugation,
    rationalQuartetPairsValue_oriented _ _ D Q _ _ _ _ _ _ true true]
  rw [samePair_total_product, samePair_left_product, div_mul_cancel, samePair_parent_ratio]
  rfl

theorem rationalQuartet_samePair_left_held_bound_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (cL cR : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
            (samePairLeftLeaves P a b r)) ρ‖ ^ 2) ≤
      8 * samePairMajorant (fieldPairCoefficientMoment (pairConjugate g cL))
        (fieldPairMoment (pairConjugate g cR)) ρ
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  simp_rw [samePairLeftLeaves_amplitude_conjugation]
  exact samePair_held_coefficient_le _ _ _ _ _ _ ρ

theorem samePairRightLeaves_amplitude_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P a b r : (ZMod p)ˣ) (cL cR : Bool) :
    rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
      (samePairRightLeaves P a b r) =
    quartetRatioValue (pairConjugate g cL) (pairConjugate g cR) true true
      (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P)
      (quartetLeftHeld D Q XL * b ^ 2) (quartetRightHeld D Q XR * r ^ 2)
      (samePairRightParentMultiplier Q XL XR P * a ^ 2) := by
  change rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
    ((a⁻¹ / b, b), (P * a / r, r)) = _
  rw [rationalTreeAmplitude_quartet_conjugation,
    rationalQuartetPairsValue_oriented _ _ D Q _ _ _ _ _ _ true true]
  rw [samePair_right_total_product, div_mul_cancel, div_mul_cancel, samePair_right_parent_ratio]
  rfl

theorem rationalQuartet_samePair_right_held_bound_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (cL cR : Bool) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
            (samePairRightLeaves P a b r)) ρ‖ ^ 2) ≤
      8 * samePairMajorant (fieldPairCoefficientMoment (pairConjugate g cR))
        (fieldPairMoment (pairConjugate g cL)) ρ
        (-rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  simp_rw [samePairRightLeaves_amplitude_conjugation]
  exact samePair_right_held_coefficient_le _ _ _ _ _ _ ρ

/-- Squared magnitude is independent even of the opposite-sibling restriction. -/
theorem rationalQuartet_fiber_secondMoment_le_any_conjugation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (c : TreeLeafTuple Bool 2) :
    (Fintype.card (TreeLeafFiber (ZMod p)ˣ 2 P) : ℝ)⁻¹ *
      (∑ m : TreeLeafFiber (ZMod p)ˣ 2 P,
        ‖rationalTreeAmplitude g D Q.tree XL XR c m.1‖ ^ 2) ≤
      8 * differenceMajorant (fieldPairMoment g) (fieldPairMoment g)
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  have h := rationalQuartet_fiber_secondMoment_le g D Q XL XR P
  simpa only [norm_rationalTreeAmplitude_sq] using h

end Ostmann

end OAI
