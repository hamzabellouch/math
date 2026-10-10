import OAI.NumberTheory.Ostmann.Characters.QuartetTestSymmetries

namespace OAI

/-! # The six possible moving-leaf pairs and their uniform local estimates -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetLocalBoundsFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

inductive QuartetMovingCase where
  | cross (left right : Bool)
  | leftPair
  | rightPair

noncomputable def quartetMovingLeaves {U : Type*} [CommGroup U]
    (choice : QuartetMovingCase) (P a b r : U) : TreeLeafTuple U 2 :=
  match choice with
  | .cross left right => crossQuartetLeaves left right P a b r
  | .leftPair => samePairLeftLeaves P a b r
  | .rightPair => samePairRightLeaves P a b r

noncomputable def quartetMovingMajorant {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (cL cR : Bool) (choice : QuartetMovingCase)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  match choice with
  | .cross left right =>
    8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
      crossPairMajorant (orientedPairBase (pairConjugate g cL) left)
        (orientedPairBase (pairConjugate g cR) right) left right ρ⁻¹ y
  | .leftPair => 8 * samePairMajorant (fieldPairCoefficientMoment (pairConjugate g cL))
      (fieldPairMoment (pairConjugate g cR)) ρ y
  | .rightPair => 8 * samePairMajorant (fieldPairCoefficientMoment (pairConjugate g cR))
      (fieldPairMoment (pairConjugate g cL)) ρ (-y)

theorem quartetMovingMajorant_nonneg {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (cL cR : Bool) (choice : QuartetMovingCase)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0 ≤ quartetMovingMajorant g cL cR choice ρ y := by
  cases choice with
  | cross left right => exact mul_nonneg (by positivity) (crossPairMajorant_nonneg _ _ _ _ _ _)
  | leftPair =>
    exact mul_nonneg (by norm_num)
      (samePairMajorant_nonneg _ _ (fun _ _ => sq_nonneg _) (fieldPairMoment_nonneg _) _ _)
  | rightPair =>
    exact mul_nonneg (by norm_num)
      (samePairMajorant_nonneg _ _ (fun _ _ => sq_nonneg _) (fieldPairMoment_nonneg _) _ _)

/-- No local-diagram estimate is assumed: this assembles the six previously
proved coefficient bounds on the actual rational-tree value. -/
theorem quartetMoving_coefficient_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) (cL cR : Bool) (choice : QuartetMovingCase)
    (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D Q.tree XL XR ((cL, !cL), (cR, !cR))
            (quartetMovingLeaves choice P a b r)) ρ‖ ^ 2) ≤
      quartetMovingMajorant g cL cR choice ρ
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  cases choice with
  | cross left right => exact rationalQuartet_cross_held_bound_conjugation g D Q XL XR P cL cR left right ρ
  | leftPair => exact rationalQuartet_samePair_left_held_bound_conjugation g D Q XL XR P cL cR ρ
  | rightPair => exact rationalQuartet_samePair_right_held_bound_conjugation g D Q XL XR P cL cR ρ

noncomputable def quartetLocalMeanError (p : ℕ) [Fact p.Prime] (ε : ℝ) : ℝ :=
  16 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 5 * ε ^ 2 +
    16 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 3 *
      (friendlyQuartetError p ε + twoBadQuartetError p ε)

theorem quartetMovingMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hflat : MixedFourierBound g ε)
    (cL cR : Bool) (choice : QuartetMovingCase) (ρ : MulChar (ZMod p) ℂ) :
    (∑ y : (ZMod p)ˣ, quartetMovingMajorant g cL cR choice ρ y) /
      (Fintype.card (ZMod p)ˣ : ℝ) ≤ quartetLocalMeanError p ε := by
  have hfirst : 0 ≤ 16 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 5 * ε ^ 2 := by positivity
  have hsecond : 0 ≤ 16 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 3 *
      (friendlyQuartetError p ε + twoBadQuartetError p ε) := by
    exact mul_nonneg (by positivity)
      (add_nonneg (friendlyQuartetError_nonneg p ε) (twoBadQuartetError_nonneg p ε))
  cases choice with
  | cross left right =>
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc]
    have h := mul_le_mul_of_nonneg_left
      (conjugated_crossPairMajorant_mean_le g hg henergy ε hε hflat cL cR left right ρ⁻¹)
      (show 0 ≤ 8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 by positivity)
    apply h.trans
    dsimp [quartetLocalMeanError]
    nlinarith
  | leftPair =>
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc]
    have h := mul_le_mul_of_nonneg_left
      (conjugated_samePairMajorant_mean_le g hg ε hε hflat henergy cL cR ρ)
      (show (0 : ℝ) ≤ 8 by norm_num)
    apply h.trans
    dsimp [quartetLocalMeanError]
    nlinarith
  | rightPair =>
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc, sum_units_neg]
    have h := mul_le_mul_of_nonneg_left
      (conjugated_samePairMajorant_mean_le g hg ε hε hflat henergy cR cL ρ)
      (show (0 : ℝ) ≤ 8 by norm_num)
    apply h.trans
    dsimp [quartetLocalMeanError]
    nlinarith

theorem quartetMovingMajorant_total_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (cL cR : Bool) (choice : QuartetMovingCase) :
    (∑ ρ : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ,
      quartetMovingMajorant g cL cR choice ρ y) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤
      8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 := by
  cases choice with
  | cross left right =>
    let F (ρ : MulChar (ZMod p) ℂ) := (∑ y : (ZMod p)ˣ,
      crossPairMajorant (orientedPairBase (pairConjugate g cL) left)
        (orientedPairBase (pairConjugate g cR) right) left right ρ y) /
          (Fintype.card (ZMod p)ˣ : ℝ)
    have hinv := (Equiv.inv (MulChar (ZMod p) ℂ)).bijective.sum_comp F
    change (∑ ρ : MulChar (ZMod p) ℂ, F ρ⁻¹) = ∑ ρ : MulChar (ZMod p) ℂ, F ρ at hinv
    have h := conjugated_crossPairMajorant_total_mean_le g hg henergy cL cR left right
    change (∑ ρ : MulChar (ZMod p) ℂ, F ρ) ≤ _ at h
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc]
    change (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2) *
      (∑ ρ : MulChar (ZMod p) ℂ, F ρ⁻¹) ≤ _
    rw [hinv]
    apply (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq
    ring
  | leftPair =>
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (conjugated_samePairMajorant_total_mean_le g hg henergy cL cR) (by norm_num)
  | rightPair =>
    simp only [quartetMovingMajorant, ← Finset.mul_sum, mul_div_assoc, sum_units_neg]
    exact mul_le_mul_of_nonneg_left
      (conjugated_samePairMajorant_total_mean_le g hg henergy cR cL) (by norm_num)

end Ostmann

end OAI
