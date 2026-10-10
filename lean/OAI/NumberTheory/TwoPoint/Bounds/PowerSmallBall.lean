import OAI.NumberTheory.TwoPoint.Bounds.TriangleKernel
import OAI.NumberTheory.TwoPoint.Bounds.PaddingDifferenceLaw

namespace OAI

/-! Integrating the `6/5` Fourier decay gives the required reciprocal-scale
small-ball bound, directly for a finite probability law. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma padding_power_integral (L : ℝ) (hL : 0 < L) :
    (∫ t in (0 : ℝ)..1, (1 + L * t) ^ (-6 / 5 : ℝ)) ≤ 5 / L := by
  have hs := intervalIntegral.integral_comp_mul_add
    (a := (0 : ℝ)) (b := 1) (fun x : ℝ => x ^ (-6 / 5 : ℝ)) hL.ne' 1
  have he := integral_rpow (a := (1 : ℝ)) (b := L + 1) (r := (-6 / 5 : ℝ))
    (Or.inr ⟨by norm_num, by
      rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ L + 1)]
      simp only [Set.mem_Icc, not_and_or]
      left
      norm_num⟩)
  have he' : (∫ x in (1 : ℝ)..L + 1, x ^ (-6 / 5 : ℝ)) =
      5 * (1 - (L + 1) ^ (-1 / 5 : ℝ)) := by
    rw [he]
    norm_num
    ring
  have hi : (∫ t in (0 : ℝ)..1, (1 + L * t) ^ (-6 / 5 : ℝ)) =
      L⁻¹ * (5 * (1 - (L + 1) ^ (-1 / 5 : ℝ))) := by
    have hs' : (∫ t in (0 : ℝ)..1, (L * t + 1) ^ (-6 / 5 : ℝ)) =
        L⁻¹ * (∫ x in (1 : ℝ)..L + 1, x ^ (-6 / 5 : ℝ)) := by
      simpa only [mul_zero, zero_add, mul_one, smul_eq_mul] using hs
    rw [he'] at hs'
    simpa only [add_comm] using hs'
  have hp : 0 ≤ (L + 1) ^ (-1 / 5 : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [hi]
  calc
    _ ≤ L⁻¹ * 5 := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hL.le)
    _ = _ := by ring

theorem FiniteLaw.unit_small_ball_of_decay {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (Z : Ω → ℝ) (L C : ℝ) (hL : 0 < L) (hC : 0 ≤ C)
    (hchar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      μ.average (fun x => Real.cos (t * Z x)) ≤ C * (1 + L * t) ^ (-6 / 5 : ℝ)) :
    μ.probability (fun x => |Z x| ≤ 1) ≤ 20 * C / L := by
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < 1 + L * t := by
    have ht0 := ht.1
    positivity
  have hg : IntervalIntegrable (fun t : ℝ => C * (1 + L * t) ^ (-6 / 5 : ℝ)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by norm_num)
    intro t ht
    have hpt := hp t ht
    have hc : ContinuousAt (fun t : ℝ => 1 + L * t) t := by fun_prop
    exact ((hc.rpow_const (Or.inl hpt.ne')).const_mul C).continuousWithinAt
  have hf : IntervalIntegrable
      (fun t : ℝ => (1 - t) * μ.average (fun x => Real.cos (t * Z x))) volume 0 1 := by
    unfold FiniteLaw.average
    exact (by fun_prop : Continuous
      (fun t : ℝ => (1 - t) * ∑ x, μ.weight x * Real.cos (t * Z x))).intervalIntegrable _ _
  have hm : (∫ t in (0 : ℝ)..1, (1 - t) * μ.average (fun x => Real.cos (t * Z x))) ≤
      C * (5 / L) := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, C * (1 + L * t) ^ (-6 / 5 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hf hg
        intro t ht
        have hh := mul_le_mul_of_nonneg_left (hchar t ht) (sub_nonneg.mpr ht.2)
        have hn : 0 ≤ C * (1 + L * t) ^ (-6 / 5 : ℝ) :=
          mul_nonneg hC (Real.rpow_nonneg (hp t ht).le _)
        nlinarith [mul_nonneg ht.1 hn]
      _ = C * (∫ t in (0 : ℝ)..1, (1 + L * t) ^ (-6 / 5 : ℝ)) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (padding_power_integral L hL) hC
  apply (μ.unit_small_ball_le Z).trans
  calc
    _ ≤ 4 * (C * (5 / L)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

theorem paddingDifference_small_ball (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (L C : ℝ) (hL : 0 < L)
    (hprime : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (3 / 4 : ℝ) * Real.log (1 + L * |t|) - C ≤ paddingOscillation Q t) :
    (paddingDifferenceLaw Q hQ).probability (fun x => |paddingDifferenceValue Q x| ≤ 1) ≤
      20 * Real.exp ((8 / 5 : ℝ) * C + 64 / 5) / L := by
  apply FiniteLaw.unit_small_ball_of_decay _ _ L _ hL (Real.exp_pos _).le
  intro t ht
  rw [paddingDifference_cosine]
  have hh := paddingCharacteristic_power_bound Q hQ L C t hL.le (hprime t ht)
  simpa only [abs_of_nonneg ht.1] using hh

end TwoPointCorrelations

end OAI
