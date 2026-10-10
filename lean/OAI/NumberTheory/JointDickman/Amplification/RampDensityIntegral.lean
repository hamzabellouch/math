import OAI.NumberTheory.JointDickman.Arithmetic.PrimeRampLocalLaw
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # The averaged profile is the integral of the ramp-weighted density -/

namespace JointDickman

open MeasureTheory Set

open Classical in
theorem clippedIntervalIntegral_eq_indicator (f : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (θ : ℝ) :
    clippedIntervalIntegral f θ a b 0 = ∫ s in a..b, if θ < s then f s else 0 := by
  have heq : (fun s => if θ < s then f s else 0) = (Ioi θ).indicator f := by
    funext s
    rfl
  rw [heq, intervalIntegral.integral_of_le hab, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, inter_comm, Ioc_inter_Ioi]
  unfold clippedIntervalIntegral
  simp only [sub_zero]
  by_cases h : max θ a ≤ b
  · rw [ite_eq_left h, intervalIntegral.integral_of_le h, max_comm]
  · rw [ite_eq_right h]
    have hempty : Ioc (max a θ) b = ∅ := Ioc_eq_empty_of_le (by simpa [max_comm] using (le_of_not_ge h))
    rw [hempty]
    simp

open Classical in
theorem indicator_density_rectangle_integrable (f : ℝ → ℝ) (hf : Continuous f)
    (lo hi a b : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => if p.1 < p.2 then f p.2 else 0)
      (uIoc lo hi ×ˢ uIoc a b) := by
  have hbase : IntegrableOn (fun p : ℝ × ℝ => f p.2) (uIcc lo hi ×ˢ uIcc a b) :=
    (hf.comp continuous_snd).continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have hsmall := hbase.mono_set (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
  have h := hsmall.indicator hset
  convert h using 1
  funext p
  rfl

open Classical in
/-- Fubini converts the average of sharp tails to the desired weighted
Lebesgue integral. Only ordinary continuity of the density is needed. -/
theorem rampIntervalIntegral_eq_density (f : ℝ → ℝ) (hf : Continuous f)
    {lo hi a b : ℝ} (hlohi : lo < hi) (hab : a ≤ b) :
    rampIntervalIntegral f lo hi a b 0 =
      ∫ s in a..b, averagingRamp lo hi s * f s := by
  unfold rampIntervalIntegral
  have hsharp : (fun θ => clippedIntervalIntegral f θ a b 0) =
      (fun θ => ∫ s in a..b, if θ < s then f s else 0) := by
    funext θ
    exact clippedIntervalIntegral_eq_indicator f hab θ
  rw [hsharp, intervalIntegral_intervalIntegral_swap (F := fun θ s => if θ < s then f s else 0)
    (a := lo) (b := hi) (c := a) (d := b) (indicator_density_rectangle_integrable f hf lo hi a b)]
  have hin (s : ℝ) : (∫ θ in lo..hi, if θ < s then f s else 0) =
      (hi - lo) * (averagingRamp lo hi s * f s) := by
    have heq : (fun θ => if θ < s then f s else 0) =
        (fun θ => (if θ < s then (1 : ℝ) else 0) * f s) := by
      funext θ
      split_ifs <;> simp
    rw [heq, intervalIntegral.integral_mul_const, integral_strict_cutoff hlohi.le]
    unfold averagingRamp
    field_simp [(sub_pos.mpr hlohi).ne']
  simp_rw [hin]
  rw [intervalIntegral.integral_const_mul]
  exact mul_div_cancel_left₀ _ (sub_pos.mpr hlohi).ne'

end JointDickman

end OAI
