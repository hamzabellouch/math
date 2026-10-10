import OAI.NumberTheory.Ostmann.Tree.PairSquareMoment
import OAI.NumberTheory.Ostmann.Characters.SquareRatioCoefficient

namespace OAI

/-! # Exposing the held product and split in a same-pair quartet -/

namespace Ostmann

open scoped BigOperators

theorem quartetRatioValue_samePair_coordinates {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (y K L q b r : (ZMod p)ˣ) :
    quartetRatioValue g h true true y (K * r ^ 2) (L * b ^ 2) q =
      if q = 1 then 0 else
        let d := (y : ZMod p) * (q : ZMod p) / ((q : ZMod p) - 1)
        fieldBottomPairValue g d ((K : ZMod p) * d * (r : ZMod p) ^ 2) *
          fieldBottomPairValue h (d - y)
            ((L : ZMod p) * (d - y) * (b : ZMod p) ^ 2) := by
  unfold quartetRatioValue ratioTest
  split_ifs
  · rfl
  · simp only [quartetLeftRatio, quartetRightRatio, ite_true, Units.val_mul,
      Units.val_pow_eq_pow_val]
    congr 2 <;> ring

/-- The two held averages cost four; the moving square pullback costs two.
All fixed unit parameters disappear from the resulting majorant. -/
theorem samePair_held_coefficient_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (y J K L : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          quartetRatioValue g h true true y (K * r ^ 2) (L * b ^ 2) (J * a ^ 2)) ρ‖ ^ 2) ≤
      8 * samePairMajorant (fieldPairCoefficientMoment g) (fieldPairMoment h) ρ y := by
  let A (d : ZMod p) := squareCharacterMass (fun χ => fieldPairCoefficientMoment g χ d) ρ
  let H (q : (ZMod p)ˣ) := if q = 1 then 0 else
    let d := (y : ZMod p) * (q : ZMod p) / ((q : ZMod p) - 1)
    A d * fieldPairMoment h (d - y)
  have hA (d : ZMod p) : 0 ≤ A d :=
    squareCharacterMass_nonneg _ (fun _ => sq_nonneg _) _
  have hH (q : (ZMod p)ˣ) : 0 ≤ H q := by
    dsimp [H]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hA _) (fieldPairMoment_nonneg h _)
  have hp (q : (ZMod p)ˣ) :
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          quartetRatioValue g h true true y (K * r ^ 2) (L * b ^ 2) q) ρ‖ ^ 2) ≤
        4 * H q := by
    simp_rw [quartetRatioValue_samePair_coordinates]
    by_cases hq : q = 1
    · simp [hq, H, mellinCoefficient]
    · simp only [hq, ite_false, H]
      simpa only [A, mul_assoc] using samePair_fixed_arguments_le g h
        ((y : ZMod p) * (q : ZMod p) / ((q : ZMod p) - 1))
        ((y : ZMod p) * (q : ZMod p) / ((q : ZMod p) - 1) - y) K L ρ
  have hsum : (∑ q : (ZMod p)ˣ, H q) =
      differenceMoment A (fieldPairMoment h) y := by
    have hzero : A 0 = 0 := by simp [A, squareCharacterMass]
    have hs := pair_ratio_sum_eq y A (fieldPairMoment h) hzero (fieldPairMoment_zero h)
    change (∑ q : (ZMod p)ˣ, H q) = ∑ x : ZMod p, A x * fieldPairMoment h (x - y)
    rw [← hs]
    apply Finset.sum_congr rfl
    intro q _
    dsimp [H]
    split_ifs with hq
    · rfl
    · have hq' : (q : ZMod p) ≠ 1 := fun h => hq (Units.ext h)
      have hd := pair_coordinate_difference (y : ZMod p) (q : ZMod p) hq'
      congr 2
      linear_combination hd
  calc
    _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ a : (ZMod p)ˣ, 4 * H (J * a ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun a _ => hp (J * a ^ 2)
    _ = 4 * (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ a : (ZMod p)ˣ, H (J * a ^ 2) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 4 * (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (2 * ∑ q : (ZMod p)ˣ, H q) :=
      mul_le_mul_of_nonneg_left (sum_square_coset_le_twice J H hH) (by positivity)
    _ = _ := by
      rw [hsum]
      change 4 * (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        (2 * differenceMoment A (fieldPairMoment h) y) =
        8 * ((Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * differenceMoment A (fieldPairMoment h) y)
      ring

end Ostmann

end OAI
