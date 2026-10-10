import OAI.NumberTheory.Ostmann.Tree.SamePairHeldAverage

namespace OAI

/-! # Swapping the two pairs and reversing the parent difference -/

namespace Ostmann

open scoped BigOperators

theorem quartetRatioValue_swap {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (y z t q : (ZMod p)ˣ) :
    quartetRatioValue g h true true y z t q =
      quartetRatioValue h g true true (-y) t z q⁻¹ := by
  by_cases hq : q = 1
  · simp [hq, quartetRatioValue, ratioTest]
  have hqi : q⁻¹ ≠ 1 := by simpa using hq
  have hqv : (q : ZMod p) ≠ 1 := fun h => hq (Units.ext h)
  have hden : (q : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr hqv
  have hi : (q : ZMod p)⁻¹ - 1 ≠ 0 := by
    intro he
    have he' : (q : ZMod p)⁻¹ = 1 := sub_eq_zero.mp he
    exact hqv (inv_eq_one.mp he')
  have hd : (-(y : ZMod p)) * (q : ZMod p)⁻¹ / ((q : ZMod p)⁻¹ - 1) =
      (y : ZMod p) * (q : ZMod p) / ((q : ZMod p) - 1) - y := by
    field_simp
    ring
  simp only [quartetRatioValue, ratioTest, hq, hqi, ite_false,
    Units.val_neg, Units.val_inv_eq_inv_val, hd,
    sub_neg_eq_add, sub_add_cancel, quartetLeftRatio, quartetRightRatio, ite_true]
  exact mul_comm _ _

/-- The same-pair estimate on the right is the left estimate with the
parent difference reversed and the product coordinate inverted. -/
theorem samePair_right_held_coefficient_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (y J K L : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          quartetRatioValue g h true true y (K * b ^ 2) (L * r ^ 2) (J * a ^ 2)) ρ‖ ^ 2) ≤
      8 * samePairMajorant (fieldPairCoefficientMoment h) (fieldPairMoment g) ρ (-y) := by
  have hfun (a b : (ZMod p)ˣ) :
      (fun r : (ZMod p)ˣ =>
        quartetRatioValue g h true true y (K * b ^ 2) (L * r ^ 2) (J * a ^ 2)) =
      (fun r : (ZMod p)ˣ =>
        quartetRatioValue h g true true (-y) (L * r ^ 2) (K * b ^ 2) (J * a ^ 2)⁻¹) :=
    funext fun r => quartetRatioValue_swap g h y _ _ _
  simp only [hfun]
  have hinv := (Equiv.inv (ZMod p)ˣ).bijective.sum_comp
    (fun a => (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
      ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
        quartetRatioValue h g true true (-y) (L * r ^ 2) (K * b ^ 2) (J⁻¹ * a ^ 2)) ρ‖ ^ 2)
  change (∑ a : (ZMod p)ˣ, _) = _ at hinv
  have hb := samePair_held_coefficient_le h g (-y) J⁻¹ L K ρ
  rw [← hinv] at hb
  simpa only [Equiv.inv_apply, mul_inv_rev, inv_pow, mul_comm J⁻¹, Units.val_neg] using hb

end Ostmann

end OAI
