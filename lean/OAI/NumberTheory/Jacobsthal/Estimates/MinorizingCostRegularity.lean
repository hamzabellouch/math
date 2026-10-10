import OAI.NumberTheory.Jacobsthal.Probability.FirstHitKernels

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.MinorizingCostRegularity

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures JointMinorization

theorem cost_strictAntiOn : StrictAntiOn cost (Ioi 0) := by
  intro t ht u hu htu
  change 0 < t at ht
  change 0 < u at hu
  unfold cost
  have hi := one_div_lt_one_div_of_lt ht htu
  exact Real.log_lt_log (by positivity) (by linarith)

theorem cost_level_null {a b k y : ℝ} (ha : 0 < a) :
    volume (Icc a b ∩ {u : ℝ | k + cost u = y}) = 0 := by
  apply Set.Subsingleton.measure_zero
  intro u hu v hv
  apply cost_strictAntiOn.injOn
    (show u ∈ Ioi 0 from lt_of_lt_of_le ha hu.1.1)
    (show v ∈ Ioi 0 from lt_of_lt_of_le ha hv.1.1)
  have huEq : k + cost u = y := hu.2
  have hvEq : k + cost v = y := hv.2
  linarith

theorem rectangleLaw_cost_level {L : ℝ} (hL : 3 ≤ L) (T y : ℝ) :
    rectangleLaw L {x : ℝ × ℝ | (pairCost T x).2 = y} = 0 := by
  have hA : MeasurableSet {x : ℝ × ℝ | (pairCost T x).2 = y} :=
    measurableSet_eq_fun (measurable_snd.comp (pairCost_measurable T)) measurable_const
  rw [rectangleLaw, rectangle, ← Measure.prod_restrict, Measure.prod_apply hA]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Eventually.of_forall
  intro t
  change (volume.restrict (Icc (L + 1) (L + 2))) {u : ℝ | T + cost t + cost u = y} = 0
  have hF : MeasurableSet {u : ℝ | T + cost t + cost u = y} :=
    measurableSet_eq_fun (measurable_const.add cost_measurable) measurable_const
  rw [Measure.restrict_apply hF, inter_comm]
  exact cost_level_null (by linarith)

theorem minorizingLaw_cost_level {L : ℝ} (hL : 3 ≤ L) (T y : ℝ) :
    minorizingLaw L T {z : ℝ × ℝ | z.2 = y} = 0 := by
  rw [minorizingLaw, Measure.map_apply (pairCost_measurable T)
    (measurableSet_eq_fun measurable_snd measurable_const)]
  exact rectangleLaw_cost_level hL T y

theorem minorizingCost_nullSingletonClass {L : ℝ} (hL : 3 ≤ L) (T : ℝ) :
    NullSingletonClass ((minorizingLaw L T).map Prod.snd) := by
  constructor
  intro y
  rw [Measure.map_apply measurable_snd (measurableSet_singleton y)]
  exact minorizingLaw_cost_level hL T y

theorem minorizingCost_countable_null {L : ℝ} (hL : 3 ≤ L) (T : ℝ)
    {C : Set ℝ} (hC : C.Countable) : ((minorizingLaw L T).map Prod.snd) C = 0 := by
  let := minorizingCost_nullSingletonClass hL T
  exact hC.measure_zero _

end NumberTheoryLean.MinorizingCostRegularity

end

end Erdos970

end OAI
