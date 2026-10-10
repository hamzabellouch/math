import OAI.Probability.InvariantIsing.Cavity.CavityTiltedTail

namespace OAI

/-! Prior tails required for removing the spatially restricted denominator
floor. The available physical and finite-cascade fourth moments suffice. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma cavity_fourth_tail_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (R : X → ℝ)
    (hi : Integrable (fun x => R x^4) ν) {a : ℝ} (ha : 0 < a) :
    ν.real {x | a < |R x|} ≤ (∫ x, R x^4 ∂ν) / a^4 := by
  have hs : {x | a < |R x|} ⊆ {x | a^4 ≤ R x^4} := by
    intro x hx
    change a^4 ≤ R x^4
    simpa only [pow_abs, abs_of_nonneg (by positivity : 0 ≤ R x^4)] using
      pow_le_pow_left₀ ha.le hx.le 4
  apply (le_div_iff₀ (pow_pos ha 4)).mpr
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all ν fun x => by positivity : ∀ᵐ x ∂ν, 0 ≤ R x^4) hi (a^4)
  have ht := mul_le_mul_of_nonneg_left (measureReal_mono (μ := ν) hs) (pow_nonneg ha.le 4)
  nlinarith

lemma measurable_cavityPriorTail {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (R : Ω × X → ℝ) (hR : Measurable R) (a : ℝ) :
    Measurable (fun ω => (ν ω).real {x | a < |R (ω,x)|}) := by
  have hs : MeasurableSet {p : Ω × X | a < |R p|} :=
    measurableSet_lt measurable_const hR.abs
  have he ω : (∫ x, (if a < |R (ω,x)| then (1:ℝ) else 0) ∂ν ω) =
      (ν ω).real {x | a < |R (ω,x)|} := by
    have hsω : MeasurableSet {x | a < |R (ω,x)|} := hs.preimage measurable_prodMk_left
    simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] using
      (integral_indicator_one (μ := ν ω) hsω)
  have hm := measurable_cavityWeightNormalizer ν hν
    (fun p : Ω × X => if a < |R p| then (1:ℝ) else 0)
    (Measurable.ite hs measurable_const measurable_const)
  simpa only [cavityWeightNormalizer, he] using hm

theorem cavity_random_prior_fourth_tail {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (R : Ω × X → ℝ) (hR : Measurable R)
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => R (ω,x)^4) (ν ω))
    (hmi : Integrable (fun ω => ∫ x, R (ω,x)^4 ∂ν ω) P)
    {M a : ℝ} (ha : 0 < a)
    (hM : (∫ ω, ∫ x, R (ω,x)^4 ∂ν ω ∂P) ≤ M) :
    (∫ ω, (ν ω).real {x | a < |R (ω,x)|} ∂P) ≤ M/a^4 := by
  have hiT : Integrable (fun ω => (ν ω).real {x | a < |R (ω,x)|}) P :=
    integrable_of_measurable_abs_le (measurable_cavityPriorTail ν hν R hR a)
      (c := 1) (fun _ => by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  have hh := integral_mono_ae hiT (hmi.div_const (a^4))
    (hi.mono fun ω hω => cavity_fourth_tail_le (ν ω) (fun x => R (ω,x)) hω ha)
  rw [integral_div] at hh
  exact hh.trans (div_le_div_of_nonneg_right hM (pow_nonneg ha.le 4))

end InvariantIsing

end

end OAI
