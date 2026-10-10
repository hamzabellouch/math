import OAI.NumberTheory.JointDickman.Arithmetic.HarmonicSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace OAI

/-! # Quantitative partial summation for coefficient tests -/

namespace JointDickman

open MeasureTheory Finset

/-- A C¹ test loses only its value and first-derivative bounds when a
summatory estimate is transferred to a weighted sum. -/
theorem weighted_counting_error_le (w : ℕ → ℝ) (F φ φ' : ℝ → ℝ)
    {a b ε M N : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hε : 0 ≤ ε) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.Icc a b)) (hF : ContinuousOn F (Set.Icc a b))
    (hvalue : ∀ t ∈ Set.Icc a b, |φ t| ≤ M)
    (hderiv : ∀ t ∈ Set.Icc a b, |φ' t| ≤ N)
    (herr : ∀ t ∈ Set.Icc a b, |finiteCountingFunction w t - F t| ≤ ε * t) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n * w n) -
      (φ b * F b - φ a * F a - ∫ t in a..b, φ' t * F t)| ≤
      ε * b * (2 * M + N * (b - a)) := by
  have hd : ContinuousOn (deriv φ) (Set.Icc a b) := hφ'.congr (fun t ht => (hφ t ht).deriv)
  have hAbel := sum_mul_eq_sub_sub_integral_mul (c := w) ha hab
    (fun t ht => (hφ t ht).differentiableAt) hd.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hAbel
  have hiw : IntervalIntegrable (fun t => φ' t * finiteCountingFunction w t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact integrableOn_mul_sum_Icc w ha hφ'.integrableOn_Icc
  have hiF : IntervalIntegrable (fun t => φ' t * F t) volume a b :=
    (hφ'.mul hF).intervalIntegrable_of_Icc hab
  have hid : (∫ t in a..b, deriv φ t * ∑ n ∈ Icc 0 ⌊t⌋₊, w n) =
      ∫ t in a..b, φ' t * finiteCountingFunction w t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    dsimp only
    rw [(hφ t ht).deriv]
    rfl
  rw [hid] at hAbel
  have hdiff : (∫ t in a..b, φ' t * finiteCountingFunction w t) -
      (∫ t in a..b, φ' t * F t) =
      ∫ t in a..b, φ' t * (finiteCountingFunction w t - F t) := by
    rw [← intervalIntegral.integral_sub hiw hiF]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hE (t : ℝ) (ht : t ∈ Set.Icc a b) : |finiteCountingFunction w t - F t| ≤ ε * b :=
    (herr t ht).trans (mul_le_mul_of_nonneg_left ht.2 hε)
  have hboundary (t : ℝ) (ht : t ∈ Set.Icc a b) :
      |φ t * (finiteCountingFunction w t - F t)| ≤ M * (ε * b) := by
    rw [abs_mul]
    exact mul_le_mul (hvalue t ht) (hE t ht) (abs_nonneg _) hM
  have hint : |∫ t in a..b, φ' t * (finiteCountingFunction w t - F t)| ≤ N * (ε * b) * (b - a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t => φ' t * (finiteCountingFunction w t - F t))
      (C := N * (ε * b)) (fun t ht => by
        have ht' : t ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc ht
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hderiv t ht') (hE t ht') (abs_nonneg _) hN)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hh
  have heq : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n * w n) -
      (φ b * F b - φ a * F a - ∫ t in a..b, φ' t * F t) =
      φ b * (finiteCountingFunction w b - F b) - φ a * (finiteCountingFunction w a - F a) -
        ∫ t in a..b, φ' t * (finiteCountingFunction w t - F t) := by
    rw [← hdiff, hAbel]
    unfold finiteCountingFunction
    ring
  rw [heq]
  calc
    _ ≤ |φ b * (finiteCountingFunction w b - F b)| +
        |φ a * (finiteCountingFunction w a - F a)| +
        |∫ t in a..b, φ' t * (finiteCountingFunction w t - F t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ M * (ε * b) + M * (ε * b) + N * (ε * b) * (b - a) :=
      add_le_add (add_le_add (hboundary b ⟨hab, le_rfl⟩) (hboundary a ⟨le_rfl, hab⟩)) hint
    _ = _ := by ring

end JointDickman

end OAI
