import OAI.NumberTheory.DirichletL.EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

namespace OAI

noncomputable section
namespace SevenEighths.LatticeSummability
open EisensteinTheta

theorem normForm_nonneg (x y : ℝ) : 0 ≤ normForm x y := by
  unfold normForm
  nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]

theorem normForm_eq_zero_iff (x y : ℝ) : normForm x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    unfold normForm at h
    have hx : x ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
    have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
    exact ⟨sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy⟩
  · rintro ⟨rfl, rfl⟩
    simp [normForm]

theorem normForm_ge_half_norm_sq (n : ℤ × ℤ) :
    (1 / 2 : ℝ) * ‖n‖ ^ 2 ≤ normForm n.1 n.2 := by
  rw [Prod.norm_def, ← Int.norm_cast_real, ← Int.norm_cast_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  unfold normForm
  rcases le_total |(n.1 : ℝ)| |(n.2 : ℝ)| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg ((n.1 : ℝ) - n.2), sq_nonneg (n.1 : ℝ)]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg ((n.1 : ℝ) - n.2), sq_nonneg (n.2 : ℝ)]

theorem summable_pair_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable (fun n : ℤ × ℤ => ‖n‖ ^ (-k)) := by
  have h := (finTwoArrowEquiv ℤ).symm.summable_iff.mpr
    (EisensteinSeries.summable_one_div_norm_rpow hk)
  have hn (n : ℤ) : (n.natAbs : ℝ) = ‖n‖ := by
    exact congrArg (fun x : NNReal => (x : ℝ)) (NNReal.natCast_natAbs n)
  simpa only [finTwoArrowEquiv_symm_apply, Function.comp_def,
    EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.norm_def, Nat.cast_max, hn] using h

theorem summable_normForm_neg_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => normForm n.1 n.2 ^ (-σ)) := by
  have hmajor := (summable_pair_norm_rpow (k := 2 * σ) (by linarith)).mul_left
    ((1 / 2 : ℝ) ^ (-σ))
  apply Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (normForm_nonneg _ _) _) _ hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    simp [normForm, Real.zero_rpow (by linarith : -σ ≠ 0),
      Real.zero_rpow (by linarith : -(2 * σ) ≠ 0)]
  · have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
    calc
      normForm n.1 n.2 ^ (-σ) ≤ ((1 / 2 : ℝ) * ‖n‖ ^ 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (normForm_ge_half_norm_sq n)
          (by linarith)
      _ = (1 / 2 : ℝ) ^ (-σ) * ‖n‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg _)]
        congr 1
        rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring

theorem summable_one_div_normForm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => 1 / normForm n.1 n.2 ^ σ) := by
  simpa only [Real.rpow_neg (normForm_nonneg _ _), one_div] using
    summable_normForm_neg_rpow hσ

theorem summable_weighted_normForm {w : ℤ × ℤ → ℂ} {C σ : ℝ}
    (hw : ∀ n, ‖w n‖ ≤ C) (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => ‖w n‖ / normForm n.1 n.2 ^ σ) := by
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (normForm_nonneg _ _) _)) _
    ((summable_one_div_normForm_rpow hσ).mul_left C)
  intro n
  simpa only [mul_one_div] using
    div_le_div_of_nonneg_right (hw n) (Real.rpow_nonneg (normForm_nonneg _ _) _)

end SevenEighths.LatticeSummability

end

end OAI
