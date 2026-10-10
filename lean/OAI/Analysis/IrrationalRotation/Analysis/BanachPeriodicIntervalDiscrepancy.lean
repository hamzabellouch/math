import OAI.Analysis.IrrationalRotation.Analysis.PeriodicIntervalDiscrepancy
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace OAI

namespace Invariant233.PeriodicIntervalDiscrepancy

open Set MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_integral_sub_length_smul_integral_le {f : ℝ → E}
    (hperiod : Function.Periodic f 1) (hint : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (hab : a ≤ b) :
    ‖(∫ x in a..b, f x) - (b - a) • (∫ x in (0 : ℝ)..1, f x)‖ ≤
      ∫ x in (0 : ℝ)..1, ‖f x‖ := by
  obtain ⟨L, hL, hLeq⟩ := exists_dual_vector'' ℝ
    ((∫ x in a..b, f x) - (b - a) • (∫ x in (0 : ℝ)..1, f x))
  have hLf : IntervalIntegrable (fun x => L (f x)) volume 0 1 :=
    ⟨L.integrable_comp hint.1, L.integrable_comp hint.2⟩
  have hperiodL : Function.Periodic (fun x => L (f x)) 1 := by
    intro x
    change L (f (x + 1)) = L (f x)
    rw [hperiod x]
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have h := abs_integral_sub_length_mul_integral_le hperiodL hLf hab
  rw [L.intervalIntegral_comp_comm (hint' a b), L.intervalIntegral_comp_comm hint,
    ← smul_eq_mul, ← L.map_smul, ← L.map_sub, hLeq] at h
  simp only [RCLike.ofReal_real_eq_id, id_eq, abs_of_nonneg (norm_nonneg _)] at h
  refine h.trans (intervalIntegral.integral_mono_on (by norm_num) hLf.abs hint.norm ?_)
  intro x _
  calc
    |L (f x)| = ‖L (f x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖L‖ * ‖f x‖ := L.le_opNorm _
    _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖f x‖ := one_mul _

omit [CompleteSpace E] in

theorem integral_cond_Ioc_smul {f : ℝ → E} {a b : ℝ} (hab : a < b) :
    (∫ x, f x ∂ProbabilityTheory.cond volume (Ioc a b)) =
      (b - a)⁻¹ • ∫ x in a..b, f x := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    Real.volume_Ioc, ENNReal.toReal_ofReal (sub_pos.mpr hab).le,
    intervalIntegral.integral_of_le hab.le]

theorem norm_integral_cond_sub_integral_le {f : ℝ → E}
    (hperiod : Function.Periodic f 1) (hint : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (hab : a < b) :
    ‖(∫ x, f x ∂ProbabilityTheory.cond volume (Ioc a b)) -
        (∫ x in (0 : ℝ)..1, f x)‖ ≤
      (b - a)⁻¹ * ∫ x in (0 : ℝ)..1, ‖f x‖ := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  rw [integral_cond_Ioc_smul hab]
  have heq : (b - a)⁻¹ • (∫ x in a..b, f x) - (∫ x in (0 : ℝ)..1, f x) =
      (b - a)⁻¹ • ((∫ x in a..b, f x) -
        (b - a) • (∫ x in (0 : ℝ)..1, f x)) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hlen.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlen)]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_sub_length_smul_integral_le hperiod hint hab.le)
    (inv_nonneg.mpr hlen.le)

omit [NormedSpace ℝ E] [CompleteSpace E] in

theorem intervalIntegrable_fract_comp_banach {g : ℝ → E}
    (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (fun x => g (Int.fract x)) volume 0 1 := by
  apply hg.congr_uIoo
  simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using (fract_comp_eqOn g).symm

omit [CompleteSpace E] in

theorem integral_cond_Ioc_mul_banach {f : ℝ → E} {a b k : ℝ}
    (hab : a < b) (hk : 0 < k) :
    (∫ x, f (k * x) ∂ProbabilityTheory.cond volume (Ioc a b)) =
      ∫ x, f x ∂ProbabilityTheory.cond volume (Ioc (k * a) (k * b)) := by
  rw [integral_cond_Ioc_smul hab, integral_cond_Ioc_smul (mul_lt_mul_of_pos_left hab hk),
    intervalIntegral.integral_comp_mul_left f hk.ne', smul_smul]
  rw [← mul_sub, mul_inv_rev]

theorem uniform_angle_test_norm_le {N n : ℝ} (hN : 0 < N) (hn : 0 < n)
    {g : ℝ → E} (hg : IntervalIntegrable g volume 0 1) :
    ‖(∫ θ, g (Int.fract (n * θ))
        ∂ProbabilityTheory.cond volume (Icc (1 / N) (2 / N))) -
      (∫ t in (0 : ℝ)..1, g t)‖ ≤ (N / n) * ∫ t in (0 : ℝ)..1, ‖g t‖ := by
  have hab : (1 : ℝ) / N < 2 / N :=
    (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  have hperiod : Function.Periodic (fun x => g (Int.fract x)) 1 := by
    intro x
    simp only [Int.fract_add_one]
  have h := norm_integral_cond_sub_integral_le hperiod
    (intervalIntegrable_fract_comp_banach hg) (mul_lt_mul_of_pos_left hab hn)
  have hmean : (∫ t in (0 : ℝ)..1, g (Int.fract t)) = ∫ t in (0 : ℝ)..1, g t :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fract_comp_eqOn g)
  have hnorm : (∫ t in (0 : ℝ)..1, ‖g (Int.fract t)‖) =
      ∫ t in (0 : ℝ)..1, ‖g t‖ :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fract_comp_eqOn (fun t => ‖g t‖))
  have hlen : (n * (2 / N) - n * (1 / N))⁻¹ = N / n := by
    rw [← mul_sub, ← sub_div, show (2 : ℝ) - 1 = 1 by norm_num]
    field_simp
  rw [hmean, hnorm, hlen] at h
  rw [ModuloIntervalMeasure.cond_Icc_eq_cond_Ioc,
    integral_cond_Ioc_mul_banach (f := fun x => g (Int.fract x)) hab hn]
  exact h

omit [NormedSpace ℝ E] [CompleteSpace E] in

theorem integrable_uniform_angle_test {N n : ℝ} (hN : 0 < N) (hn : n ≠ 0)
    {g : ℝ → E} (hg : IntervalIntegrable g volume 0 1) :
    Integrable (fun θ => g (Int.fract (n * θ)))
      (ProbabilityTheory.cond volume (Icc (1 / N) (2 / N))) := by
  have hab : (1 : ℝ) / N < 2 / N :=
    (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  have hperiod : Function.Periodic (fun x => g (Int.fract x)) 1 := by
    intro x
    simp only [Int.fract_add_one]
  have hint := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0)
    (intervalIntegrable_fract_comp_banach hg) (n * (1 / N)) (n * (2 / N))
  have hint' : IntervalIntegrable (fun θ => g (Int.fract (n * θ))) volume
      (1 / N) (2 / N) := by
    convert hint.comp_mul_left (c := n) using 1 <;> field_simp
  rw [ModuloIntervalMeasure.cond_Icc_eq_cond_Ioc, ProbabilityTheory.cond]
  apply hint'.1.smul_measure
  apply ENNReal.inv_ne_top.mpr
  rw [Real.volume_Ioc]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))

end Invariant233.PeriodicIntervalDiscrepancy

end OAI
