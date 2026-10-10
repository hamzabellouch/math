import OAI.NumberTheory.Ostmann.Dirichlet.PrimeSeriesTailBound

namespace OAI

noncomputable section
namespace Ostmann.Dirichlet
open Filter

theorem ordinaryPrimeTail_manuscript_bound {X η : ℝ} (hX : 1 < X) :
    (∑' n : ℕ, if n.Prime ∧ X ^ (1 / 2 - 5 * η : ℝ) < (n : ℝ)
      then Real.log n / (n : ℝ) ^ (1 + 10 / Real.log X) else 0) ≤
      Real.log 4 * (Real.log X / 10 + 1) * Real.exp (-5 + 50 * η) := by
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hσ : 1 < 1 + 10 / Real.log X := by
    have hd := div_pos (by norm_num : (0 : ℝ) < 10) hlog
    linarith
  have hQ : 0 < X ^ (1 / 2 - 5 * η : ℝ) := Real.rpow_pos_of_pos hX0 _
  have h := ordinaryPrimeTail_le hσ hQ
  have hpow : (X ^ (1 / 2 - 5 * η : ℝ)) ^ (1 - (1 + 10 / Real.log X)) =
      Real.exp (-5 + 50 * η) := by
    rw [← Real.rpow_mul hX0.le, Real.rpow_def_of_pos hX0]
    congr 1
    field_simp [hlog.ne']
    ring
  have hfac : Real.log 4 * (1 + 10 / Real.log X) / ((1 + 10 / Real.log X) - 1) =
      Real.log 4 * (Real.log X / 10 + 1) := by
    field_simp [hlog.ne']
    ring
  simpa only [hpow, hfac] using h

lemma exp_split_tail_le {η : ℝ} (hη : η ≤ 1 / 1000) :
    Real.exp (-5 + 50 * η) ≤ 1 / 100 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 99 / 20) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have h100 : (100 : ℝ) ≤ Real.exp (99 / 20) := by linarith
  calc
    Real.exp (-5 + 50 * η) ≤ Real.exp (-(99 / 20 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / Real.exp (99 / 20) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) h100

theorem ordinaryPrimeTail_manuscript_small {X η : ℝ} (hX : 1 < X)
    (hlog : 100 ≤ Real.log X) (hη : η ≤ 1 / 1000) :
    (∑' n : ℕ, if n.Prime ∧ X ^ (1 / 2 - 5 * η : ℝ) < (n : ℝ)
      then Real.log n / (n : ℝ) ^ (1 + 10 / Real.log X) else 0) ≤
      (3 / 1000 : ℝ) * Real.log X := by
  have h := ordinaryPrimeTail_manuscript_bound (η := η) hX
  have hlog4 : Real.log 4 ≤ 2 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hfac : 0 ≤ Real.log X / 10 + 1 := by linarith
  have h1 := mul_le_mul_of_nonneg_right hlog4 hfac
  have h2 := mul_le_mul h1 (exp_split_tail_le hη) (Real.exp_pos _).le
    (show 0 ≤ 2 * (Real.log X / 10 + 1) by positivity)
  nlinarith

theorem eventually_ordinaryPrimeTail_manuscript_small {η : ℝ} (hη : η ≤ 1 / 1000) :
    ∀ᶠ X : ℝ in atTop,
      (∑' n : ℕ, if n.Prime ∧ X ^ (1 / 2 - 5 * η : ℝ) < (n : ℝ)
        then Real.log n / (n : ℝ) ^ (1 + 10 / Real.log X) else 0) ≤
        (3 / 1000 : ℝ) * Real.log X := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 100]
    with X hX hlog
  exact ordinaryPrimeTail_manuscript_small hX hlog hη

end Ostmann.Dirichlet

end

end OAI
