import OAI.Probability.InvariantIsing.Core.UnitIntervalMomentUniqueness

namespace OAI

/-! Positive resolvents determine probability measures on the nonnegative real line. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

def resolventUnit (x : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨positiveResolventTest 1 x, (positiveResolventTest_bound (t := 1) (by norm_num) x).1,
    by simpa only [one_div_one] using (positiveResolventTest_bound (t := 1) (by norm_num) x).2⟩

lemma continuous_resolventUnit : Continuous resolventUnit :=
  (continuous_positiveResolventTest (by norm_num : (0 : ℝ) < 1)).subtype_mk _

lemma resolventUnit_inverse {x : ℝ} (hx : 0 ≤ x) : 1/(resolventUnit x : ℝ)-1 = x := by
  change 1/(1/(1+max x 0))-1=x
  rw [max_eq_left hx,one_div_one_div]
  ring

lemma resolventUnit_map_inverse (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x) :
    (μ.map resolventUnit).map (fun x : Icc (0 : ℝ) 1 => 1/(x : ℝ)-1) = μ := by
  have hm : Measurable (fun x : Icc (0 : ℝ) 1 => 1/(x : ℝ)-1) := by fun_prop
  rw [Measure.map_map hm continuous_resolventUnit.measurable]
  calc
    μ.map ((fun x : Icc (0 : ℝ) 1 => 1/(x : ℝ)-1) ∘ resolventUnit) = μ.map id := by
      apply Measure.map_congr
      filter_upwards [hμ] with x hx
      exact resolventUnit_inverse hx
    _ = μ := Measure.map_id

theorem positiveResolvent_unique (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    (h : ∀ t : ℝ, 0 < t → (∫ x, positiveResolventTest t x ∂μ) =
      ∫ x, positiveResolventTest t x ∂ν) : μ = ν := by
  have : IsProbabilityMeasure (μ.map resolventUnit) :=
    (Measure.isProbabilityMeasure_map_iff continuous_resolventUnit.measurable.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (ν.map resolventUnit) :=
    (Measure.isProbabilityMeasure_map_iff continuous_resolventUnit.measurable.aemeasurable).mpr inferInstance
  have he : μ.map resolventUnit = ν.map resolventUnit := by
    apply unitInterval_moments_unique
    intro n
    have hc : Continuous (fun x : Icc (0 : ℝ) 1 => (x : ℝ)^n) := continuous_subtype_val.pow n
    rw [integral_map continuous_resolventUnit.measurable.aemeasurable hc.aestronglyMeasurable,
      integral_map continuous_resolventUnit.measurable.aemeasurable hc.aestronglyMeasurable]
    cases n with
    | zero => simp only [pow_zero,integral_const,probReal_univ,smul_eq_mul,mul_one]
    | succ n => exact positiveResolvent_moments_eq μ ν h n 1 (by norm_num)
  have hi := congrArg (fun η : Measure (Icc (0 : ℝ) 1) =>
    η.map (fun x : Icc (0 : ℝ) 1 => 1/(x : ℝ)-1)) he
  rwa [resolventUnit_map_inverse μ hμ,resolventUnit_map_inverse ν hν] at hi

end InvariantIsing

end

end OAI
