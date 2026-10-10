import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367
namespace DependentWeight

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

theorem integral_mul_le_of_exceptional_set
    {z g : Ω → ℝ} {s : Set Ω} {a M : ℝ}
    (hs : MeasurableSet s) (hz : Integrable z μ)
    (hzg : Integrable (fun x => z x * g x) μ)
    (ha : 0 ≤ a)
    (hz_nonneg : ∀ᵐ x ∂μ, 0 ≤ z x)
    (hz_bound : ∀ᵐ x ∂μ, z x ≤ M)
    (hg_bound : ∀ᵐ x ∂μ, g x ≤ 1)
    (hg_good : ∀ᵐ x ∂μ, x ∉ s → g x ≤ a) :
    (∫ x, z x * g x ∂μ) ≤ a * (∫ x, z x ∂μ) + M * μ.real s := by
  have hind : Integrable (s.indicator (fun _ : Ω => M)) μ :=
    (integrable_const M).indicator hs
  have hpoint : (fun x => z x * g x) ≤ᵐ[μ]
      (fun x => a * z x + s.indicator (fun _ : Ω => M) x) := by
    filter_upwards [hz_nonneg, hz_bound, hg_bound, hg_good] with x hz0 hzM hg1 hga
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]
      have hprod : z x * g x ≤ M :=
        (mul_le_mul_of_nonneg_left hg1 hz0).trans (by simpa using hzM)
      exact hprod.trans (le_add_of_nonneg_left (mul_nonneg ha hz0))
    · simp only [Set.indicator_of_notMem hxs, add_zero]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hga hxs) hz0
  calc
    (∫ x, z x * g x ∂μ) ≤
        ∫ x, a * z x + s.indicator (fun _ : Ω => M) x ∂μ :=
      integral_mono_ae hzg ((hz.const_mul a).add hind) hpoint
    _ = a * (∫ x, z x ∂μ) + M * μ.real s := by
      rw [integral_add (hz.const_mul a) hind, integral_const_mul,
        integral_indicator_const M hs]
      simp [smul_eq_mul, mul_comm]

theorem integral_mul_le_of_exceptional_probability
    {z g : Ω → ℝ} {s : Set Ω} {a M ε : ℝ}
    (hs : MeasurableSet s) (hz : Integrable z μ)
    (hzg : Integrable (fun x => z x * g x) μ)
    (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hz_nonneg : ∀ᵐ x ∂μ, 0 ≤ z x)
    (hz_bound : ∀ᵐ x ∂μ, z x ≤ M)
    (hg_bound : ∀ᵐ x ∂μ, g x ≤ 1)
    (hg_good : ∀ᵐ x ∂μ, x ∉ s → g x ≤ a)
    (hprob : μ.real s ≤ ε) :
    (∫ x, z x * g x ∂μ) ≤ a * (∫ x, z x ∂μ) + M * ε := by
  exact (integral_mul_le_of_exceptional_set hs hz hzg ha hz_nonneg hz_bound
    hg_bound hg_good).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprob hM))

theorem integral_mul_le_of_tail_probability
    {z g : Ω → ℝ} {a M ε : ℝ}
    (hz : Integrable z μ) (hg : Measurable g)
    (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hz_nonneg : ∀ᵐ x ∂μ, 0 ≤ z x)
    (hz_bound : ∀ᵐ x ∂μ, z x ≤ M)
    (hg_nonneg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hg_bound : ∀ᵐ x ∂μ, g x ≤ 1)
    (hprob : μ.real {x | a < g x} ≤ ε) :
    (∫ x, z x * g x ∂μ) ≤ a * (∫ x, z x ∂μ) + M * ε := by
  have hnorm : ∀ᵐ x ∂μ, ‖g x‖ ≤ (1 : ℝ) := by
    filter_upwards [hg_nonneg, hg_bound] with x hx0 hx1
    simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  refine integral_mul_le_of_exceptional_probability
    (measurableSet_lt measurable_const hg) hz
    (hz.mul_bdd hg.aestronglyMeasurable hnorm) ha hM
    hz_nonneg hz_bound hg_bound ?_ hprob
  exact Filter.Eventually.of_forall (fun x hx => le_of_not_gt hx)

theorem integral_sq_mul_le_of_tail_probability
    {f g : Ω → ℝ} {a M ε : ℝ}
    (hf : MemLp f 2 μ) (hg : Measurable g)
    (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hf_bound : ∀ᵐ x ∂μ, f x ^ 2 ≤ M)
    (hg_nonneg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hg_bound : ∀ᵐ x ∂μ, g x ≤ 1)
    (hprob : μ.real {x | a < g x} ≤ ε) :
    (∫ x, f x ^ 2 * g x ∂μ) ≤
      a * (∫ x, f x ^ 2 ∂μ) + M * ε := by
  exact integral_mul_le_of_tail_probability hf.integrable_sq hg ha hM
    (Filter.Eventually.of_forall fun x => sq_nonneg (f x)) hf_bound
    hg_nonneg hg_bound hprob

theorem integral_mul_le_of_dominated_tail
    {z g h : Ω → ℝ} {C τ M ε : ℝ}
    (hz : Integrable z μ) (hg : Measurable g)
    (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hM : 0 ≤ M)
    (hz_nonneg : ∀ᵐ x ∂μ, 0 ≤ z x)
    (hz_bound : ∀ᵐ x ∂μ, z x ≤ M)
    (hg_nonneg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hg_bound : ∀ᵐ x ∂μ, g x ≤ 1)
    (hdom : ∀ᵐ x ∂μ, g x ≤ C * h x)
    (hprob : μ.real {x | τ ≤ h x} ≤ ε) :
    (∫ x, z x * g x ∂μ) ≤ (C * τ) * (∫ x, z x ∂μ) + M * ε := by
  have htail : μ.real {x | C * τ < g x} ≤ μ.real {x | τ ≤ h x} := by
    apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono_ae
    filter_upwards [hdom] with x hx
    intro hx_tail
    by_contra hx_bad
    have hh : h x ≤ τ := (lt_of_not_ge hx_bad).le
    have hmul := mul_le_mul_of_nonneg_left hh hC
    exact (not_lt_of_ge (hx.trans hmul)) hx_tail
  exact integral_mul_le_of_tail_probability hz hg (mul_nonneg hC hτ) hM
    hz_nonneg hz_bound hg_nonneg hg_bound (htail.trans hprob)

end DependentWeight
end Problem367

end

end OAI
