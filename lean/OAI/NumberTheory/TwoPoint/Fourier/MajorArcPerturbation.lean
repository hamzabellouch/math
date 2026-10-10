import OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! A finite partial-summation form of the major-arc frequency perturbation.
The error uses the actual shorter windows before averaging the origin;
no frequency supremum is moved inside an integral. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma major_arc_abel_bound (a w : ℕ → ℂ) (N : ℕ) (L : ℝ)
    (hw : ∀ n, ‖w n‖ ≤ 1)
    (hstep : ∀ n, ‖w (n + 1) - w n‖ ≤ L) :
    ‖∑ n ∈ range N, a n * w n‖ ≤ ‖∑ n ∈ range N, a n‖ +
      L * ∑ n ∈ range (N - 1), ‖∑ j ∈ range (n + 1), a j‖ := by
  have he := sum_range_by_parts' a w N
  simp only [smul_eq_mul] at he
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hw _)
  · calc
      _ ≤ ∑ n ∈ range (N - 1),
          ‖(∑ j ∈ range (n + 1), a j) * (w (n + 1) - w n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range (N - 1), L * ‖∑ j ∈ range (n + 1), a j‖ := by
        apply sum_le_sum
        intro n _
        rw [norm_mul, mul_comm L]
        exact mul_le_mul_of_nonneg_left (hstep n) (norm_nonneg _)
      _ = _ := (mul_sum _ _ _).symm

lemma major_arc_character_step (β : ℝ) (n : ℕ) :
    ‖additiveCharacter β (n + 1) - additiveCharacter β n‖ ≤
      2 * Real.pi * |β| := by
  have he : additiveCharacter β (n + 1) - additiveCharacter β n =
      additiveCharacter β n * (additiveCharacter β 1 - 1) := by
    rw [additiveCharacter_nat_add]
    ring
  rw [he, norm_mul, norm_additiveCharacter, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * β)
  have harg : additiveCharacter β 1 = Complex.exp (Complex.I * (2 * Real.pi * β : ℝ)) := by
    unfold additiveCharacter
    congr 1
    push_cast
    ring
  rw [harg]
  convert h using 1
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num

lemma major_arc_frequency_perturbation (a : ℕ → ℂ) (H v : ℕ) (α β : ℝ) :
    ‖shortExponentialSum a H (α + β) v‖ ≤
      ‖shortExponentialSum a H α v‖ + 2 * Real.pi * |β| *
        ∑ h ∈ range (H - 1), ‖shortExponentialSum a (h + 1) α v‖ := by
  have hb := major_arc_abel_bound
    (fun n => a (v + n + 1) * additiveCharacter α (v + n + 1))
    (fun n => additiveCharacter β (v + n + 1)) H (2 * Real.pi * |β|)
    (fun n => (norm_additiveCharacter β _).le)
    (fun n => by
      simpa only [Nat.add_assoc] using major_arc_character_step β (v + n + 1))
  simp only [shortExponentialSum_at_nat, sum_Icc_shift]
  convert hb using 1
  apply congrArg norm
  apply sum_congr rfl
  intro n _
  rw [additiveCharacter_add]
  ring

theorem major_arc_integral_perturbation (a : ℕ → ℂ) (X H : ℕ) (α β : ℝ) :
    shortExponentialIntegral a X H (α + β) ≤
      shortExponentialIntegral a X H α + 2 * Real.pi * |β| *
        ∑ h ∈ range (H - 1), shortExponentialIntegral a X (h + 1) α := by
  simp only [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X, (‖shortExponentialSum a H α v‖ + 2 * Real.pi * |β| *
        ∑ h ∈ range (H - 1), ‖shortExponentialSum a (h + 1) α v‖) :=
      sum_le_sum (fun v _ => major_arc_frequency_perturbation a H v α β)
    _ = _ := by rw [sum_add_distrib, ← mul_sum, sum_comm]

lemma major_arc_integral_perturbation_uniform (a : ℕ → ℂ) (X H : ℕ)
    (hH : 0 < H) (α β K : ℝ) (hK : 0 ≤ K)
    (hprefix : ∀ h : ℕ, 1 ≤ h → h ≤ H → shortExponentialIntegral a X h α ≤ K) :
    shortExponentialIntegral a X H (α + β) ≤
      (1 + 2 * Real.pi * |β| * H) * K := by
  apply (major_arc_integral_perturbation a X H α β).trans
  have hs : (∑ h ∈ range (H - 1), shortExponentialIntegral a X (h + 1) α) ≤
      (H : ℝ) * K := by
    calc
      _ ≤ ∑ _h ∈ range (H - 1), K := by
        apply sum_le_sum
        intro h hh
        exact hprefix (h + 1) (by omega) (by have := mem_range.mp hh; omega)
      _ = ((H - 1 : ℕ) : ℝ) * K := by simp
      _ ≤ (H : ℝ) * K := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.sub_le H 1) hK
  calc
    _ ≤ K + 2 * Real.pi * |β| * ((H : ℝ) * K) :=
      add_le_add (hprefix H hH le_rfl) (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
