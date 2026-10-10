import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspExhaustion

namespace OAI

/-! A common square-integrable majorant for the exhaustion errors. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspExhaustion_sub_one_norm (T : Finset SL(2,Eisenstein))
    (n : ℕ) (q : CubicThetaQuotient) :
    ‖cubicThetaCuspExhaustion T n q-1‖≤2+(T.card:ℝ) := by
  have h := (norm_sub_le (cubicThetaCuspExhaustion T n q) 1).trans
    (add_le_add (cubicThetaCuspExhaustion_norm T n q) (le_refl ‖(1:ℂ)‖))
  exact h.trans_eq (by rw [norm_one]; ring)

lemma cubicThetaCuspExhaustion_value_bound (T : Finset SL(2,Eisenstein))
    (F : CubicThetaSection) (n : ℕ) (q : CubicThetaQuotient) :
    ‖cubicThetaSectionRepresentative (cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F) q-
      cubicThetaSectionRepresentative F q‖^2≤
      (2+(T.card:ℝ))^2*‖cubicThetaSectionRepresentative F q‖^2 := by
  have he : cubicThetaSectionRepresentative (cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F) q-
      cubicThetaSectionRepresentative F q=
      (cubicThetaCuspExhaustion T n q-1)*cubicThetaSectionRepresentative F q := by
    unfold cubicThetaSectionRepresentative
    change cubicThetaCuspExhaustion T n (cubicThetaQuotientMap (cubicThetaBorelSection q))*_ -_=_
    rw [cubicThetaBorelSection_rightInverse]
    ring
  rw [he,norm_mul,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (_root_.norm_nonneg _) (cubicThetaCuspExhaustion_sub_one_norm T n q) 2

lemma cubicThetaCuspExhaustion_gradient_bound (T : Finset SL(2,Eisenstein))
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ∃ B≥0, ∀ (n : ℕ) (q : CubicThetaQuotient),
      ‖cubicThetaGradientRepresentative (cubicThetaSectionCutoff (cubicThetaCuspExhaustion T n) F) q-
        cubicThetaGradientRepresentative F q‖^2≤
      2*(2+(T.card:ℝ))^2*‖cubicThetaGradientRepresentative F q‖^2+
        2*B*‖cubicThetaSectionRepresentative F q‖^2 := by
  obtain ⟨B,hB,hbound⟩ := cubicThetaCuspExhaustion_energy T
  refine ⟨B,hB,fun n q => ?_⟩
  have h := cubicThetaSectionCutoff_gradient_error (cubicThetaCuspExhaustion T n)
    ((cubicThetaCuspExhaustion_smooth T n).of_le (by simp)) F hF (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse] at h
  change _≤2*‖cubicThetaCuspExhaustion T n q-1‖^2*‖cubicThetaGradientRepresentative F q‖^2+
    2*‖cubicThetaSectionRepresentative F q‖^2*_
    at h
  apply h.trans
  have hs := pow_le_pow_left₀ (_root_.norm_nonneg _)
    (cubicThetaCuspExhaustion_sub_one_norm T n q) 2
  have he := hbound n (cubicThetaBorelSection q).val (cubicThetaBorelSection q).property
  have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤2))
    (sq_nonneg ‖cubicThetaGradientRepresentative F q‖)
  have h₂ := mul_le_mul_of_nonneg_left he
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg ‖cubicThetaSectionRepresentative F q‖))
  nlinarith

end CubicFirstMoment

end

end OAI
