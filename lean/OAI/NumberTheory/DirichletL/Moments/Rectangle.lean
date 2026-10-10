import OAI.NumberTheory.DirichletL.Moments.Height

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentRectangle
open CenteredMomentPrimary CenteredMomentMask CenteredMomentTwist

def idealWeight (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (I : Ideal O) : ℂ :=
  (if IsCoprime I R then (1 : ℂ) else 0) *
    primaryIdealCharacter c χ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t)

theorem idealWeight_mul (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (I J : Ideal O) :
    idealWeight c χ R t (I * J) = idealWeight c χ R t I * idealWeight c χ R t J := by
  have hpow : ((Ideal.absNorm I : ℂ) * (Ideal.absNorm J : ℂ)) ^ (Complex.I * t) =
      (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * (Ideal.absNorm J : ℂ) ^ (Complex.I * t) := by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg
      (Nat.cast_nonneg (Ideal.absNorm I) : (0 : ℝ) ≤ Ideal.absNorm I)
      (Nat.cast_nonneg (Ideal.absNorm J) : (0 : ℝ) ≤ Ideal.absNorm J) (Complex.I * t)
  simp only [idealWeight, map_mul, Nat.cast_mul, hpow, IsCoprime.mul_left_iff]
  by_cases hI : IsCoprime I R <;> by_cases hJ : IsCoprime J R <;> simp [hI, hJ] ; ring

def idealRectangle (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O) : ℂ :=
  W₁ ((Ideal.absNorm I : ℝ) / X₁) * W₂ ((Ideal.absNorm J : ℝ) / X₂) -
    W₁ ((Ideal.absNorm I : ℝ) / Y₁) * W₂ ((Ideal.absNorm J : ℝ) / Y₂)

theorem twistedMaskedSum_eq_weight (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (W : ℝ → ℂ) (X : ℝ) :
    twistedMaskedSum c χ R W t X =
      ∑' I : Ideal O, idealWeight c χ R t I * W ((Ideal.absNorm I : ℝ) / X) := by
  apply tsum_congr
  intro I
  unfold idealWeight
  ring

theorem actual_rectangle_sum
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      idealWeight c χ R t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      twistedMaskedSum c χ R W₁ t X₁ * twistedMaskedSum c χ R W₂ t X₂ -
        twistedMaskedSum c χ R W₁ t Y₁ * twistedMaskedSum c χ R W₂ t Y₂ := by
  let w := idealWeight c χ R t
  let f₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal O) :
      idealWeight c χ R t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [idealWeight_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal O) : (∑' J : Ideal O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal O, f₂ J) - g₁ I * (∑' J : Ideal O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [twistedMaskedSum_eq_weight]
  rfl

end SevenEighths.CenteredMomentRectangle
end

end OAI
