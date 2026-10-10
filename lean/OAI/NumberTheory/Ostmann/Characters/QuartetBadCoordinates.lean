import OAI.NumberTheory.Ostmann.Characters.QuartetFriendlyCoordinates
import OAI.NumberTheory.Ostmann.Tree.PairOrientationValue

namespace OAI

/-! # Shared-entry square cancellation in the bad quartet orientations -/

namespace Ostmann

/-- The inverse ratio uses the square of the first, now held, entry. -/
theorem pair_inverse_ratio_held {p : ℕ} [Fact p.Prime]
    (D s s₁ s₂ C₁ C₂ V X m₁ m₂ : (ZMod p)ˣ) :
    ((s₁ / s₂) * ((X * C₂ * m₂) / (V * C₁ * m₁)))⁻¹ =
      ((D * s₂ / (s₁ * s)) * (V * C₁) ^ 2 * m₁ ^ 2) *
        rationalTreeArgument s (C₁ * C₂) D V X (m₁ * m₂) := by
  unfold rationalTreeArgument
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val]
  field_simp

/-- The common reconstructed entry has the exact square needed to cancel
one difference from each child pair. The child products need only agree. -/
theorem rationalQuartet_shared_square {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (V XL XR M N : (ZMod p)ˣ) :
    V ^ 2 = (Q.sL * Q.sR / (Q.s * D * Q.u ^ 2)) *
      rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR (M * N) /
        (rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL M *
          rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR N) := by
  unfold rationalTreeArgument
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  field_simp

/-- Algebraic cancellation producing `lambda / e` in the bad orientation. -/
theorem bad_ratio_of_shared_square {p : ℕ} [Fact p.Prime]
    (K C y V d e m : (ZMod p)ˣ) (hV : V ^ 2 = C * y / (d * e)) :
    (K * (V * m) ^ 2) * d = (K * C * y) * m ^ 2 / e := by
  rw [mul_pow, hV]
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  field_simp

/-- The corresponding cancellation on the right produces `lambda / d`. -/
theorem bad_ratio_of_shared_square_right {p : ℕ} [Fact p.Prime]
    (K C y V d e m : (ZMod p)ˣ) (hV : V ^ 2 = C * y / (d * e)) :
    (K * (V * m) ^ 2) * e = (K * C * y) * m ^ 2 / d := by
  apply bad_ratio_of_shared_square K C y V e d m
  simpa only [mul_comm] using hV

noncomputable def quartetSharedConstant {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) : (ZMod p)ˣ :=
  Q.sL * Q.sR / (Q.s * D * Q.u ^ 2)

noncomputable def quartetLeftBadHeld {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (D * Q.s₂ / (Q.s₁ * Q.sL) * Q.C₁ ^ 2) * quartetSharedConstant D Q *
    rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P

noncomputable def quartetRightBadHeld {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ) (XL XR P : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (D * Q.s₄ / (Q.s₃ * Q.sR) * Q.C₃ ^ 2) * quartetSharedConstant D Q *
    rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P

/-- Holding the reconstructed entry on the left gives exactly the bad ratio. -/
theorem rationalQuartet_left_bad_ratio {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (V XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) :
    ((Q.s₁ / Q.s₂) * ((XL * Q.C₂ * m₂) / (V * Q.C₁ * m₁)))⁻¹ =
      (quartetLeftBadHeld D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) * m₁ ^ 2) /
        rationalTreeArgument Q.sR (Q.u * Q.CR) D V XR (m₃ * m₄) := by
  rw [pair_inverse_ratio_held D Q.sL Q.s₁ Q.s₂ Q.C₁ Q.C₂ V XL m₁ m₂]
  rw [Q.left_product]
  have hreshape :
      ((D * Q.s₂ / (Q.s₁ * Q.sL)) * (V * Q.C₁) ^ 2 * m₁ ^ 2) =
        (D * Q.s₂ / (Q.s₁ * Q.sL) * Q.C₁ ^ 2) * (V * m₁) ^ 2 := by
    simp only [mul_pow, mul_assoc, mul_left_comm, mul_comm]
  rw [hreshape]
  exact bad_ratio_of_shared_square _ (quartetSharedConstant D Q) _ V _ _ m₁
    (rationalQuartet_shared_square D Q V XL XR (m₁ * m₂) (m₃ * m₄))

/-- The right held reconstructed entry gives the other bad ratio. -/
theorem rationalQuartet_right_bad_ratio {p : ℕ} [Fact p.Prime]
    (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (V XL XR m₁ m₂ m₃ m₄ : (ZMod p)ˣ) :
    ((Q.s₃ / Q.s₄) * ((XR * Q.C₄ * m₄) / (V * Q.C₃ * m₃)))⁻¹ =
      (quartetRightBadHeld D Q XL XR ((m₁ * m₂) * (m₃ * m₄)) * m₃ ^ 2) /
        rationalTreeArgument Q.sL (Q.u * Q.CL) D V XL (m₁ * m₂) := by
  rw [pair_inverse_ratio_held D Q.sR Q.s₃ Q.s₄ Q.C₃ Q.C₄ V XR m₃ m₄]
  rw [Q.right_product]
  have hreshape :
      ((D * Q.s₄ / (Q.s₃ * Q.sR)) * (V * Q.C₃) ^ 2 * m₃ ^ 2) =
        (D * Q.s₄ / (Q.s₃ * Q.sR) * Q.C₃ ^ 2) * (V * m₃) ^ 2 := by
    simp only [mul_pow, mul_assoc, mul_left_comm, mul_comm]
  rw [hreshape]
  exact bad_ratio_of_shared_square_right _ (quartetSharedConstant D Q) _ V _ _ m₃
    (rationalQuartet_shared_square D Q V XL XR (m₁ * m₂) (m₃ * m₄))

end Ostmann

end OAI
