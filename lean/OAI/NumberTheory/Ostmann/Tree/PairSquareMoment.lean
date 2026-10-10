import OAI.NumberTheory.Ostmann.Characters.FieldPairMoment

namespace OAI

/-! # Square-coordinate estimates for one moving bottom pair -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance pairSquareFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def fieldPairCoefficientMoment {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (d : ZMod p) : ℝ :=
  ‖mellinCoefficient (fun t => fieldBottomPairValue g d t) χ‖ ^ 2

@[simp] theorem fieldPairCoefficientMoment_zero {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) :
    fieldPairCoefficientMoment g χ 0 = 0 := by
  simp [fieldPairCoefficientMoment, mellinCoefficient]

theorem sum_fieldPairCoefficientMoment {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ, fieldPairCoefficientMoment g χ d) = fieldPairMoment g d := by
  unfold fieldPairCoefficientMoment fieldPairMoment
  exact mellin_parseval (fun t : (ZMod p)ˣ => fieldBottomPairValue g d t)

theorem mellinCoefficient_mul_const {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)ˣ → ℂ) (c : ℂ) (χ : MulChar (ZMod p) ℂ) :
    mellinCoefficient (fun t => f t * c) χ = mellinCoefficient f χ * c := by
  unfold mellinCoefficient
  have ht (t : (ZMod p)ˣ) : f t * c * conj (χ t) = (f t * conj (χ t)) * c := by ring
  simp_rw [ht]
  rw [← Finset.sum_mul]
  ring

/-- Multiplication by the difference can be absorbed into the fixed square
coset; the zero difference is handled by the zero extension. -/
theorem fieldPair_scaled_square_coefficient_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) (K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
      fieldBottomPairValue g d ((K : ZMod p) * d * (r : ZMod p) ^ 2)) ρ‖ ^ 2 ≤
      2 * squareCharacterMass (fun χ => fieldPairCoefficientMoment g χ d) ρ := by
  classical
  by_cases hd : d = 0
  · simp [hd, mellinCoefficient, squareCharacterMass]
  · let k : (ZMod p)ˣ := K * Units.mk0 d hd
    have h := mellinCoefficient_square_pullback_bound Finset.univ
      (mellinCoefficient (fun t => fieldBottomPairValue g d t))
      (fun t => fieldBottomPairValue g d t)
      (fun t => (mellin_inversion (fun t => fieldBottomPairValue g d t) t).symm) k ρ
    simpa only [k, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
      fieldPairCoefficientMoment, squareCharacterMass] using h

theorem fieldPair_scaled_square_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) (K : (ZMod p)ˣ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ b : (ZMod p)ˣ, ‖fieldBottomPairValue g d
        ((K : ZMod p) * d * (b : ZMod p) ^ 2)‖ ^ 2) ≤ 2 * fieldPairMoment g d := by
  by_cases hd : d = 0
  · simp [hd]
  · let k : (ZMod p)ˣ := K * Units.mk0 d hd
    have h := sum_square_coset_le_twice k
      (fun t => ‖fieldBottomPairValue g d t‖ ^ 2) (fun _ => sq_nonneg _)
    have h' := mul_le_mul_of_nonneg_left h
      (show 0 ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ by positivity)
    simpa only [k, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
      fieldPairMoment, mul_left_comm] using h'

/-- First average the held pair's split, while the two pair differences
remain fixed. This costs two square fibers and the moving-pair coefficient. -/
theorem samePair_fixed_arguments_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (d e : ZMod p) (K L : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ b : (ZMod p)ˣ,
      ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
        fieldBottomPairValue g d ((K : ZMod p) * d * (r : ZMod p) ^ 2) *
        fieldBottomPairValue h e ((L : ZMod p) * e * (b : ZMod p) ^ 2)) ρ‖ ^ 2) ≤
      4 * squareCharacterMass (fun χ => fieldPairCoefficientMoment g χ d) ρ *
        fieldPairMoment h e := by
  let A := squareCharacterMass (fun χ => fieldPairCoefficientMoment g χ d) ρ
  have hA : 0 ≤ A := squareCharacterMass_nonneg _ (fun _ => sq_nonneg _) _
  simp_rw [mellinCoefficient_mul_const, norm_mul, mul_pow]
  calc
    _ ≤ (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ b : (ZMod p)ˣ,
        (2 * A) * ‖fieldBottomPairValue h e
          ((L : ZMod p) * e * (b : ZMod p) ^ 2)‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_right (fieldPair_scaled_square_coefficient_le g d K ρ)
          (sq_nonneg _)
    _ = (2 * A) * ((Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        ∑ b : (ZMod p)ˣ, ‖fieldBottomPairValue h e
          ((L : ZMod p) * e * (b : ZMod p) ^ 2)‖ ^ 2) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (2 * A) * (2 * fieldPairMoment h e) :=
      mul_le_mul_of_nonneg_left (fieldPair_scaled_square_mean_le h e L) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
