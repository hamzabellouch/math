import OAI.Geometry.EinsteinFour.JacobiExpectedLog

namespace OAI

/-! Jensen's scalar exponential step, with all logarithms and integrals
taken only for strictly positive continuous determinants. -/
namespace PositiveEinsteinFour.Jacobi
open MeasureTheory
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exp_integral_log_le_integral (f : Ω → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 < f x) : Real.exp (∫ x, Real.log (f x) ∂μ) ≤ ∫ x, f x ∂μ := by
  let m := ∫ x, Real.log (f x) ∂μ
  have hi : Integrable (fun x => Real.log (f x)) μ :=
    (hf.log (fun x => (hpos x).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfi := hf.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have his : Integrable (fun x => Real.log (f x) - m) μ := hi.sub (integrable_const m)
  have hb (x : Ω) : Real.exp m * (1 + (Real.log (f x) - m)) ≤ f x := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (Real.log (f x) - m))
      (Real.exp_pos m).le
    have he : Real.exp m * Real.exp (Real.log (f x) - m) = f x := by
      rw [← Real.exp_add, add_sub_cancel, Real.exp_log (hpos x)]
    rw [he] at h
    convert h using 1
    ring
  have hj := integral_mono (((integrable_const 1).add his).const_mul
    (Real.exp m)) hfi hb
  rw [integral_const_mul] at hj
  change Real.exp m * (∫ x, (1 + (Real.log (f x) - m)) ∂μ) ≤ _ at hj
  rw [integral_add (integrable_const 1) his,
    integral_sub hi (integrable_const m)] at hj
  simpa [m] using hj

end
end PositiveEinsteinFour.Jacobi

end OAI
