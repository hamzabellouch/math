import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorUniform

namespace OAI

/-! The auxiliary size cutoffs in the uniform short-factor estimate are automatic. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma shortFactorPolynomial_uniform_quadratic_size :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ (F X Y : ℝ) (A : EisensteinArithmeticFunction)
      (u : Eisenstein → ℂ), ShortArithmeticFactor F A → 1 ≤ X → X ≤ Y → T ≤ Y →
      (∀ n ∈ primaryElementBall X, ‖u n‖ ≤ 1) →
      ‖primaryIdealPolynomial X A u‖ ≤ Y^2 := by
  obtain ⟨C,hC,hbound⟩ := shortFactorPolynomial_norm_small_power
    (show (0:ℝ) < 1/2 by norm_num)
  refine ⟨max 1 (C^2),le_max_left _ _,?_⟩
  intro F X Y A u hA hX hXY hTY hu
  have hY : 1 ≤ Y := (le_max_left _ _).trans hTY
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hCsq : C^2 ≤ Y := (le_max_right _ _).trans hTY
  have hCroot : C ≤ Real.sqrt Y := (Real.le_sqrt hC.le hYp.le).mpr hCsq
  have hCpow : C ≤ Y^(1/2:ℝ) := by simpa only [Real.sqrt_eq_rpow] using hCroot
  calc
    _ ≤ C*X^(1+(1/2:ℝ)) := hbound F X A hA hX u hu
    _ ≤ C*Y^(1+(1/2:ℝ)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans hX) hXY (by norm_num)) hC.le
    _ ≤ Y^(1/2:ℝ)*Y^(1+(1/2:ℝ)) := mul_le_mul_of_nonneg_right hCpow
      (Real.rpow_nonneg hYp.le _)
    _ = Y^2 := by rw [← Real.rpow_add hYp]; norm_num

lemma primary_gram_rows_card_quadratic (S : Finset Eisenstein) {Y : ℝ}
    (hY : 36 ≤ Y) (hS : ∀ p ∈ S, gramDyad Y p) : (S.card:ℝ) ≤ Y^2 := by
  have hY0 : 0 ≤ Y := by linarith
  have hsub : S ⊆ nonzeroNormBall (2*Y) := by
    intro p hp
    exact mem_nonzeroNormBall.mpr ⟨(hS p hp).2.2.2.le,primary_ne_zero (hS p hp).1⟩
  have hcard := (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)).trans
    (nonzeroNormBall_card_le (show 0 ≤ 2*Y by positivity))
  nlinarith

lemma balanced_rows_card_quadratic (S : Finset (Eisenstein × Eisenstein)) {Y : ℝ}
    (hY : 324 ≤ Y)
    (hS : ∀ p ∈ S, PrimarySquarefreePair p ∧ norm p.1 ≤ Y^(1/3:ℝ) ∧
      norm p.2 ≤ Y^(1/3:ℝ)) : (S.card:ℝ) ≤ Y^2 := by
  have hY₁ : 1 ≤ Y := by linarith
  have hYp : 0 < Y := zero_lt_one.trans_le hY₁
  have h := balanced_pair_card S (Real.rpow_nonneg hYp.le (1/3:ℝ))
    (fun p hp => ⟨(hS p hp).1.1,(hS p hp).1.2.1,(hS p hp).2⟩)
  have hp : (Y^(1/3:ℝ))^2 = Y^(2/3:ℝ) := by
    rw [← Real.rpow_mul_natCast hYp.le]
    norm_num
  rw [hp] at h
  have hle : Y^(2/3:ℝ) ≤ Y := by
    convert Real.rpow_le_rpow_of_exponent_le hY₁ (show (2/3:ℝ) ≤ 1 by norm_num) using 1
    rw [Real.rpow_one]
  exact h.trans ((mul_le_mul_of_nonneg_left hle (by norm_num)).trans (by nlinarith))

end CubicFirstMoment

end

end OAI
