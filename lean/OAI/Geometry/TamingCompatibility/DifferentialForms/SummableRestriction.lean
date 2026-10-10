import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.SummableCutoff

namespace OAI

section

noncomputable section
open Filter MeasureTheory Finset
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma weighted_saturation_tendsto (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n))
    (μ : Measure X) (a : X → ℝ) (ha : Integrable a μ) (n : ℕ) :
    Tendsto (fun N => ∫ x, saturation c n N x * a x ∂μ) atTop
      (𝓝 (∫ x, tailLimit c n x * a x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖a x‖)
    (fun N => (measurable_saturation c hm n N).aestronglyMeasurable.mul ha.aestronglyMeasurable) ha.norm
  · intro N
    apply Eventually.of_forall
    intro x
    change ‖saturation c n N x * a x‖ ≤ ‖a x‖
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (saturation_nonneg c hc n N x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (saturation_le_one c n N x)
  · exact Eventually.of_forall (fun x => (saturation_tendsto_tail c hc n x).mul tendsto_const_nhds)

lemma weighted_tail_tendsto (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n))
    (μ : Measure X) (a : X → ℝ) (ha : Integrable a μ) :
    Tendsto (fun n => ∫ x, tailLimit c n x * a x ∂μ) atTop
      (𝓝 (∫ x in exceptional c, a x ∂μ)) := by
  have hlim : ∀ x, Tendsto (fun n => tailLimit c n x * a x) atTop
      (𝓝 ((exceptional c).indicator a x)) := by
    intro x
    convert (tail_tendsto_indicator c x).mul (tendsto_const_nhds (x := a x)) using 1
    by_cases hx : x ∈ exceptional c <;> simp [hx]
  have hD := tendsto_integral_of_dominated_convergence (fun x => ‖a x‖)
    (fun n => (measurable_tail c hc hm n).aestronglyMeasurable.mul ha.aestronglyMeasurable) ha.norm
    (fun n => Eventually.of_forall (fun x => show ‖tailLimit c n x * a x‖ ≤ ‖a x‖ from by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (tail_nonneg c hc n x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (tail_le_one c hc n x)))
    (Eventually.of_forall hlim)
  rwa [integral_indicator (measurable_exceptional c hc hm)] at hD

lemma restriction_zero_of_tail_bounds
    (c : ℕ → X → ℝ) (d : ℕ → Y → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hd : ∀ n y, 0 ≤ d n y)
    (hcm : ∀ n, Measurable (c n)) (hdm : ∀ n, Measurable (d n))
    (μ : Measure X) (ν : Measure Y) (a : X → ℝ) (b : Y → ℝ)
    (ha : Integrable a μ) (hb : Integrable b ν)
    (hnull : ν (exceptional d) = 0)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (hes : Summable e)
    (hbound : ∀ n N, |(∫ x, saturation c n N x * a x ∂μ) +
      (∫ y, saturation d n N y * b y ∂ν)| ≤ ∑ k ∈ Finset.range N, e (k+n)) :
    ∫ x in exceptional c, a x ∂μ = 0 := by
  have htail (n : ℕ) : |(∫ x, tailLimit c n x * a x ∂μ)+
      (∫ y, tailLimit d n y * b y ∂ν)| ≤ ∑' k, e (k+n) := by
    apply le_of_tendsto (((weighted_saturation_tendsto c hc hcm μ a ha n).add
      (weighted_saturation_tendsto d hd hdm ν b hb n)).abs)
    apply Eventually.of_forall
    intro N
    exact (hbound n N).trans (((summable_nat_add_iff n).2 hes).sum_le_tsum
      (Finset.range N) (fun k _ => he (k+n)))
  have hlim := ((weighted_tail_tendsto c hc hcm μ a ha).add
    (weighted_tail_tendsto d hd hdm ν b hb)).abs
  have hbzero : ∫ y in exceptional d, b y ∂ν = 0 := by
    rw [Measure.restrict_eq_zero.mpr hnull,integral_zero_measure]
  rw [hbzero,add_zero] at hlim
  have hh := le_of_tendsto_of_tendsto hlim (tendsto_sum_nat_add e)
    (Eventually.of_forall htail)
  exact abs_nonpos_iff.mp hh
end TamingCompatibility.SummableCutoff

end
end

end OAI
