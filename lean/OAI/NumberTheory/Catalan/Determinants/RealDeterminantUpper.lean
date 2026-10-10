import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Energy.RealTwoSheetIntegralBound
import OAI.NumberTheory.Catalan.Estimates.RealEnergyMajorantExponential
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneGlobalBounds
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoGlobalBounds
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoNorm

namespace OAI


noncomputable section
open Filter
open scoped Topology

namespace InternalCatalan

def realDeterminantSheetPrefactor (N : ℕ) : ℝ :=
  max ((1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N)
    ((3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2))

def realDeterminantPrefactor (N : ℕ) : ℝ :=
  (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N / ((n N).factorial : ℝ) ^ 2

theorem realDeterminantSheetPrefactor_nonneg (N : ℕ) :
    0 ≤ realDeterminantSheetPrefactor N := by
  apply le_trans _ (le_max_left _ _)
  exact pow_nonneg (by positivity) _

theorem realDeterminantPrefactor_nonneg (N : ℕ) : 0 ≤ realDeterminantPrefactor N := by
  exact div_nonneg
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (realDeterminantSheetPrefactor_nonneg N)) (sq_nonneg _)

theorem realDeterminant_factorial_sq_one_le (N : ℕ) :
    (1 : ℝ) ≤ ((n N).factorial : ℝ) ^ 2 := by
  have hf : (1 : ℝ) ≤ ((n N).factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (n N)))
  nlinarith [sq_nonneg (((n N).factorial : ℝ) - 1)]

theorem realDeterminantPrefactor_le_mass_mul_sheet (N : ℕ) :
    realDeterminantPrefactor N ≤ (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N := by
  exact div_le_self
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (realDeterminantSheetPrefactor_nonneg N))
    (realDeterminant_factorial_sq_one_le N)

theorem realDeterminantPrefactor_le_power {N : ℕ} (hN : 0 < N) :
    realDeterminantPrefactor N ≤
      (2 * (1 + 10 * Real.exp 12 + 3 / 2) * (n N : ℝ)) ^ n N := by
  let A : ℝ := 1 + 10 * Real.exp 12 + 3 / 2
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA32 : (3 / 2 : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [Real.exp_pos (12 : ℝ)]
  have hn1 : (1 : ℝ) ≤ n N := by
    exact_mod_cast (show 1 ≤ n N by unfold n; omega)
  have hn0 : (0 : ℝ) ≤ n N := Nat.cast_nonneg _
  have hbase : 1 + 10 * Real.exp 12 * (n N : ℝ) ≤ A * (n N : ℝ) := by
    dsimp [A]
    nlinarith only [hn1]
  have hfirst : (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N ≤
      (A * (n N : ℝ)) ^ n N :=
    pow_le_pow_left₀ (by positivity) hbase _
  have hrealpow : (n N : ℝ) ^ ((n N : ℝ) / 2) ≤ (n N : ℝ) ^ n N := by
    have hh := Real.rpow_le_rpow_of_exponent_le hn1
      (show (n N : ℝ) / 2 ≤ (n N : ℝ) by linarith)
    simpa only [Real.rpow_natCast] using hh
  have hsecond : (3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) ≤
      (A * (n N : ℝ)) ^ n N := by
    calc
      _ ≤ A ^ n N * (n N : ℝ) ^ n N :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) hA32 _)
          hrealpow (Real.rpow_nonneg hn0 _) (pow_nonneg hA0 _)
      _ = _ := (mul_pow A (n N : ℝ) (n N)).symm
  have hsheet : realDeterminantSheetPrefactor N ≤ (A * (n N : ℝ)) ^ n N :=
    max_le hfirst hsecond
  calc
    realDeterminantPrefactor N ≤ (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N :=
      realDeterminantPrefactor_le_mass_mul_sheet N
    _ ≤ (2 : ℝ) ^ n N * (A * (n N : ℝ)) ^ n N :=
      mul_le_mul_of_nonneg_left hsheet (pow_nonneg (by norm_num) _)
    _ = _ := by
      change (2 : ℝ) ^ n N * (A * (n N : ℝ)) ^ n N =
        (2 * A * (n N : ℝ)) ^ n N
      simp only [mul_pow]
      ring

theorem realDeterminantPrefactor_eventually_le_exp {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      realDeterminantPrefactor N ≤ Real.exp (d * (n N : ℝ) ^ 2) := by
  let B : ℝ := 2 * (1 + 10 * Real.exp 12 + 3 / 2)
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hconst : Tendsto (fun t : ℝ => Real.log B / t) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop _
  have hlimit : Tendsto (fun t : ℝ => (Real.log B + Real.log t) / t)
      atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using hconst.add hlog
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((tendsto_order.mp hlimit).2 d hd)
  obtain ⟨M, hM⟩ := exists_nat_gt T
  refine ⟨M + 1, ?_⟩
  intro N hNlarge
  have hN : 0 < N := by omega
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hMN : M ≤ n N := by unfold n; omega
  have hsmall := hT (n N : ℝ) (hM.le.trans (Nat.cast_le.mpr hMN))
  have hscalar : Real.log B + Real.log (n N : ℝ) ≤ d * (n N : ℝ) :=
    ((div_lt_iff₀ hn).mp hsmall).le
  have hscaled : (n N : ℝ) * (Real.log B + Real.log (n N : ℝ)) ≤
      d * (n N : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hscalar hn.le
    nlinarith only [hh]
  have hlogpower : Real.log ((B * (n N : ℝ)) ^ n N) ≤ d * (n N : ℝ) ^ 2 := by
    rw [Real.log_pow, Real.log_mul hB.ne' hn.ne']
    exact hscaled
  have hpower : realDeterminantPrefactor N ≤ (B * (n N : ℝ)) ^ n N :=
    realDeterminantPrefactor_le_power hN
  exact hpower.trans ((Real.le_exp_log _).trans (Real.exp_le_exp.mpr hlogpower))

end InternalCatalan

end



noncomputable section
open Set Filter
open scoped BigOperators

namespace InternalCatalan

theorem realDeterminant_uniform_exp_dual {lam Bx₁ Bs₁ Bx₂ Bs₂ : ℝ} (hlam : 0 ≤ lam)
    (p₁ v₁ p₂ v₂ : ℕ → ℝ)
    (hp₁ : Summable (fun j => |p₁ j|)) (hv₁ : Summable (fun j => |v₁ j|))
    (hp₂ : Summable (fun j => |p₂ j|)) (hv₂ : Summable (fun j => |v₂ j|))
    (hBx₁ : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 1 lam p₁ v₁ z ≤ Bx₁)
    (hBs₁ : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v₁ z ≤ Bs₁)
    (hBx₂ : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 2 0 p₂ v₂ z ≤ Bx₂)
    (hBs₂ : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v₂ z ≤ Bs₂)
    {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |determinant N| ≤ Real.exp ((n N : ℝ) ^ 2 *
        (max (realEnergyDualConstant 1 p₁ v₁ Bx₁ Bs₁)
          (realEnergyDualConstant 2 p₂ v₂ Bx₂ Bs₂) + d + Real.log 2 / 2)) := by
  have hd2 : 0 < d / 2 := by positivity
  obtain ⟨N₁, h₁⟩ := realEnergyMajorantOne_uniform_exp hlam p₁ v₁ hp₁ hv₁ hBx₁ hBs₁ hd2
  obtain ⟨N₂, h₂⟩ := realEnergyMajorantTwo_uniform_exp p₂ v₂ hp₂ hv₂ hBx₂ hBs₂ hd2
  obtain ⟨N₃, h₃⟩ := realDeterminantPrefactor_eventually_le_exp hd2
  refine ⟨N₁ + N₂ + N₃ + 1, ?_⟩
  intro N hlarge
  have hN : 0 < N := by omega
  let D₁ : ℝ := realEnergyDualConstant 1 p₁ v₁ Bx₁ Bs₁
  let D₂ : ℝ := realEnergyDualConstant 2 p₂ v₂ Bx₂ Bs₂
  let E₁ : ℝ := Real.exp ((n N : ℝ) ^ 2 * (D₁ + d / 2 + Real.log 2 / 2))
  let E₂ : ℝ := Real.exp ((n N : ℝ) ^ 2 * (D₂ + d / 2 + Real.log 2 / 2))
  let E : ℝ := Real.exp ((n N : ℝ) ^ 2 * (max D₁ D₂ + d / 2 + Real.log 2 / 2))
  have hI₁ : ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (((n N - 1 - 2 * g N : ℕ) : ℝ) <
        ∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) →
      realEnergyMajorantOne N x s ≤ E₁ := h₁ N (by omega)
  have hI₂ : ∀ x s : Fin (n N) → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      ((∑ i : Fin (n N), (1 - x i ^ 2) / (1 + x i ^ 2)) ≤
        ((n N - 1 - 2 * g N : ℕ) : ℝ)) →
      realEnergyMajorantTwo N x s ≤ E₂ := by
    intro x s hx hs hx0 hxi hsi _
    exact h₂ N (by omega) x s hx hs hx0 hxi hsi
  have hdet := abs_determinant_le_of_two_majorant_bounds hN
    (Real.exp_pos _).le (Real.exp_pos _).le hI₁ hI₂
  change |determinant N| ≤ realDeterminantPrefactor N * max E₁ E₂ at hdet
  have hE₁ : E₁ ≤ E := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [le_max_left D₁ D₂]) (sq_nonneg (n N : ℝ))
  have hE₂ : E₂ ≤ E := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [le_max_right D₁ D₂]) (sq_nonneg (n N : ℝ))
  have hE0 : 0 ≤ max E₁ E₂ := (Real.exp_pos _).le.trans (le_max_left _ _)
  calc
    |determinant N| ≤ realDeterminantPrefactor N * max E₁ E₂ := hdet
    _ ≤ Real.exp ((d / 2) * (n N : ℝ) ^ 2) * E :=
      mul_le_mul (h₃ N (by omega)) (max_le hE₁ hE₂) hE0 (Real.exp_pos _).le
    _ = _ := by
      dsimp [E, D₁, D₂]
      rw [← Real.exp_add]
      congr 1
      ring

theorem realDeterminant_eventually_log_dual {lam Bx₁ Bs₁ Bx₂ Bs₂ : ℝ} (hlam : 0 ≤ lam)
    (p₁ v₁ p₂ v₂ : ℕ → ℝ)
    (hp₁ : Summable (fun j => |p₁ j|)) (hv₁ : Summable (fun j => |v₁ j|))
    (hp₂ : Summable (fun j => |p₂ j|)) (hv₂ : Summable (fun j => |v₂ j|))
    (hBx₁ : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 1 lam p₁ v₁ z ≤ Bx₁)
    (hBs₁ : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v₁ z ≤ Bs₁)
    (hBx₂ : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 → realEnergyRowTrialField 2 0 p₂ v₂ z ≤ Bx₂)
    (hBs₂ : ∀ z ∈ Ioo (0 : ℝ) 1, realEnergyColumnTrialField v₂ z ≤ Bs₂)
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        max (realEnergyDualConstant 1 p₁ v₁ Bx₁ Bs₁)
          (realEnergyDualConstant 2 p₂ v₂ Bx₂ Bs₂) + d := by
  obtain ⟨M, hM⟩ := realDeterminant_uniform_exp_dual hlam p₁ v₁ p₂ v₂ hp₁ hv₁ hp₂ hv₂
    hBx₁ hBs₁ hBx₂ hBs₂ hd
  filter_upwards [eventually_ge_atTop (M + 1)] with N hNlarge
  intro hdet
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hlog := (Real.log_le_iff_le_exp (abs_pos.mpr hdet)).mpr (hM N (by omega))
  have hnorm : Real.log |determinant N| / (n N : ℝ) ^ 2 ≤
      max (realEnergyDualConstant 1 p₁ v₁ Bx₁ Bs₁)
        (realEnergyDualConstant 2 p₂ v₂ Bx₂ Bs₂) + d + Real.log 2 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    simpa only [mul_comm] using hlog
  linarith only [hnorm]

end InternalCatalan

end



noncomputable section
open Set Filter
open scoped BigOperators

namespace InternalCatalan

theorem realDeterminant_eventually_log_sup_dual {lam : ℝ} (hlam : 0 ≤ lam)
    (p₁ v₁ p₂ v₂ : ℕ → ℝ)
    (hp₁ : Summable (fun j => |p₁ j|)) (hv₁ : Summable (fun j => |v₁ j|))
    (hp₂ : Summable (fun j => |p₂ j|)) (hv₂ : Summable (fun j => |v₂ j|))
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        max (realEnergyDualConstant 1 p₁ v₁
          (realEnergyRowTrialSup 1 lam p₁ v₁) (realEnergyColumnTrialSup v₁))
          (realEnergyDualConstant 2 p₂ v₂
            (realEnergyRowTrialSup 2 0 p₂ v₂) (realEnergyColumnTrialSup v₂)) + d := by
  exact realDeterminant_eventually_log_dual hlam p₁ v₁ p₂ v₂ hp₁ hv₁ hp₂ hv₂
    (fun z hz hz0 => realEnergyRowTrialField_le_sup (by norm_num) hlam p₁ v₁ hp₁ hv₁ hz hz0)
    (fun z hz => realEnergyColumnTrialField_le_sup v₁ hv₁ hz)
    (fun z hz hz0 => realEnergyRowTrialField_le_sup (by norm_num) (le_refl 0) p₂ v₂ hp₂ hv₂ hz hz0)
    (fun z hz => realEnergyColumnTrialField_le_sup v₂ hv₂ hz) hd

def realDeterminantCertificateSupBound : ℝ :=
  max (realEnergyDualConstant 1 barrierP1 barrierV1
      (realEnergyRowTrialSup 1 barrierLambda1 barrierP1 barrierV1)
      (realEnergyColumnTrialSup barrierV1))
    (realEnergyDualConstant 2 barrierP2 barrierV2
      (realEnergyRowTrialSup 2 0 barrierP2 barrierV2) (realEnergyColumnTrialSup barrierV2))

theorem realDeterminant_eventually_log_certificate_sup {d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        realDeterminantCertificateSupBound + d := by
  exact realDeterminant_eventually_log_sup_dual barrier_lambdas.2.1
    barrierP1 barrierV1 barrierP2 barrierV2
    barrier_trials_abs_summable.2.2.1 barrier_trials_abs_summable.2.2.2
    barrier_trials_abs_summable.1 barrier_trials_abs_summable.2.1 hd

end InternalCatalan

end



noncomputable section
open Set Filter

namespace InternalCatalan

private theorem barrier_case1_row_sup_upper :
    realEnergyRowTrialSup 1 barrierLambda1 barrierP1 barrierV1 ≤
      (-13244 / 10000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyRowTrialSup
  refine csSup_le (realEnergyRowTrialField_image_nonempty _ _ _ _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa [realEnergyRowTrialField, barrierCase1X] using
    barrierCase1X_global_upper ⟨hx.1.1, hx.1.2, hx.2⟩

private theorem barrier_case1_column_sup_upper :
    realEnergyColumnTrialSup barrierV1 ≤ (-14280 / 10000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyColumnTrialSup
  refine csSup_le (realEnergyColumnTrialField_image_nonempty _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa only [realEnergyColumnTrialField, barrierCase1Y] using barrierCase1Y_global_upper hx

private theorem barrier_case2_row_sup_upper :
    realEnergyRowTrialSup 2 0 barrierP2 barrierV2 ≤
      (-98399 / 100000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyRowTrialSup
  refine csSup_le (realEnergyRowTrialField_image_nonempty _ _ _ _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa [realEnergyRowTrialField, barrierCase2X, barrierLambda2,
    show (2 : ℝ) * 2 = 4 by norm_num] using
    barrierCase2X_global_upper ⟨hx.1.1, hx.1.2, hx.2⟩

private theorem barrier_case2_column_sup_upper :
    realEnergyColumnTrialSup barrierV2 ≤ (-160890 / 100000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyColumnTrialSup
  refine csSup_le (realEnergyColumnTrialField_image_nonempty _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa only [realEnergyColumnTrialField, barrierCase2Y] using barrierCase2Y_global_upper hx

theorem realDeterminantCaseOneDual_sharp_lt :
    realEnergyDualConstant 1 barrierP1 barrierV1
      (realEnergyRowTrialSup 1 barrierLambda1 barrierP1 barrierV1)
      (realEnergyColumnTrialSup barrierV1) < -(2296789875 / 1000000000 : ℝ) := by
  unfold realEnergyDualConstant
  nlinarith only [barrier_case1_norm_coarse_upper, barrier_case1_row_sup_upper,
    barrier_case1_column_sup_upper, barrier_one_coarse_total_sharp_lt]

theorem realDeterminantCaseTwoDual_sharp_lt :
    realEnergyDualConstant 2 barrierP2 barrierV2
      (realEnergyRowTrialSup 2 0 barrierP2 barrierV2)
      (realEnergyColumnTrialSup barrierV2) < -(2290939875 / 1000000000 : ℝ) := by
  unfold realEnergyDualConstant
  nlinarith only [barrier_case2_norm_coarse_upper, barrier_case2_row_sup_upper,
    barrier_case2_column_sup_upper, barrier_two_coarse_total_sharp_lt]

theorem realDeterminantCertificateSupBound_sharp_lt :
    realDeterminantCertificateSupBound < -(2290939875 / 1000000000 : ℝ) := by
  unfold realDeterminantCertificateSupBound
  apply max_lt
  · exact lt_trans realDeterminantCaseOneDual_sharp_lt (by norm_num)
  · exact realDeterminantCaseTwoDual_sharp_lt

theorem realDeterminantCertificateSupBound_lt :
    realDeterminantCertificateSupBound < -(22909 / 10000 : ℝ) :=
  lt_trans realDeterminantCertificateSupBound_sharp_lt (by norm_num)

theorem eventually_realDeterminant_log_upper_sharp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        -(2290939875 / 1000000000 : ℝ) + ε := by
  filter_upwards [realDeterminant_eventually_log_certificate_sup hε] with N hN
  intro hnonzero
  linarith only [hN hnonzero, realDeterminantCertificateSupBound_sharp_lt]

theorem eventually_realDeterminant_abs_upper_sharp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, |determinant N| ≤
      Real.exp ((n N : ℝ) ^ 2 *
        (-(2290939875 / 1000000000 : ℝ) + Real.log 2 / 2 + ε)) := by
  filter_upwards [eventually_realDeterminant_log_upper_sharp hε,
    eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  by_cases hz : determinant N = 0
  · rw [hz, abs_zero]
    exact (Real.exp_pos _).le
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hn2 : (0 : ℝ) < (n N : ℝ) ^ 2 := sq_pos_of_pos hn
  have hlog : Real.log |determinant N| ≤ (n N : ℝ) ^ 2 *
      (-(2290939875 / 1000000000 : ℝ) + Real.log 2 / 2 + ε) := by
    have hb : Real.log |determinant N| / (n N : ℝ) ^ 2 ≤
        -(2290939875 / 1000000000 : ℝ) + Real.log 2 / 2 + ε := by
      linarith [hN hz]
    simpa only [mul_comm] using (div_le_iff₀ hn2).mp hb
  calc
    |determinant N| = Real.exp (Real.log |determinant N|) :=
      (Real.exp_log (abs_pos.mpr hz)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem eventually_realDeterminant_log_upper :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 <
        -(22909 / 10000 : ℝ) := by
  have hd : 0 < (-(22909 / 10000 : ℝ) - realDeterminantCertificateSupBound) / 2 := by
    linarith [realDeterminantCertificateSupBound_lt]
  filter_upwards [realDeterminant_eventually_log_certificate_sup hd] with N hN
  intro hnonzero
  have hupper := hN hnonzero
  linarith [realDeterminantCertificateSupBound_lt]

end InternalCatalan

end

end OAI
