import OAI.Analysis.CircleDomains.Topology.PathImageCount
import OAI.Analysis.CircleDomains.Probability.PathHitLaws
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Flagged intersections count each image point once. Tonelli bounds
these actual counts by the level-band width times its hit probability,
so repeated visits introduce no extra factor in the final bound. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathImageCount_inter_eq_tsum (S T : Set X) (γ : C(PathTime, X)) :
    pathImageCount (S ∩ T) γ =
      ∑' x : S, if x.val ∈ range γ ∩ T then (1 : ℝ≥0∞) else 0 := by
  classical
  rw [pathImageCount]
  symm
  rw [tsum_subtype S (fun x => if x ∈ range γ ∩ T then (1 : ℝ≥0∞) else 0)]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ S <;> simp [Set.indicator, hx]

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem mean_flag_intersection_count_le
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (S : Set X) (hS : S.Countable) (a : X → ℝ≥0∞)
    (hband : ∀ x ∈ S, volume {t : UnitAddCircle | (t, x) ∈ H} ≤ a x)
    (μ : ProbabilityMeasure C(PathTime, X)) :
    (∫⁻ t : UnitAddCircle, ∫⁻ γ, pathImageCount (S ∩ {x | (t, x) ∈ H}) γ
      ∂(μ : Measure _)) ≤ ∑' x : S, a x.val * pathHitProbability μ x.val := by
  classical
  let : Countable S := hS.to_subtype
  have hlevel (x : S) : MeasurableSet {t : UnitAddCircle | (t, x.val) ∈ H} :=
    (hH.preimage (continuous_id.prodMk continuous_const)).measurableSet
  have hhit (x : S) : MeasurableSet {γ : C(PathTime, X) | x.val ∈ range γ} :=
    (isClosed_paths_hitting x.val).measurableSet
  have hi (t : UnitAddCircle) :
      (∫⁻ γ, pathImageCount (S ∩ {x | (t, x) ∈ H}) γ ∂(μ : Measure _)) =
        ∑' x : S, (if (t, x.val) ∈ H then (1 : ℝ≥0∞) else 0) * pathHitProbability μ x.val := by
    simp_rw [pathImageCount_inter_eq_tsum]
    have hprod (x : S) (γ : C(PathTime, X)) :
        (if x.val ∈ range γ ∩ {x | (t, x) ∈ H} then (1 : ℝ≥0∞) else 0) =
        (if (t, x.val) ∈ H then (1 : ℝ≥0∞) else 0) * (if x.val ∈ range γ then 1 else 0) := by
      by_cases hl : (t, x.val) ∈ H <;> by_cases hh : x.val ∈ range γ <;> simp [hl, hh]
    simp_rw [hprod]
    rw [lintegral_tsum]
    · apply tsum_congr
      intro x
      rw [lintegral_const_mul]
      · congr 1
        change (∫⁻ γ, Set.indicator {γ : C(PathTime, X) | x.val ∈ range γ} 1 γ
          ∂(μ : Measure C(PathTime, X))) =
          (μ : Measure C(PathTime, X)) {γ : C(PathTime, X) | x.val ∈ range γ}
        exact lintegral_indicator_one (hhit x)
      · exact (measurable_one.indicator (hhit x))
    · intro x
      exact (measurable_const.mul (measurable_one.indicator (hhit x))).aemeasurable
  simp_rw [hi]
  rw [lintegral_tsum]
  · apply ENNReal.tsum_le_tsum
    intro x
    change (∫⁻ t, {t : UnitAddCircle | (t, x.val) ∈ H}.indicator 1 t *
      pathHitProbability μ x.val) ≤ _
    rw [lintegral_mul_const _ (measurable_one.indicator (hlevel x)), lintegral_indicator_one (hlevel x)]
    exact mul_le_mul' (hband x.val x.property) le_rfl
  · intro x
    exact ((measurable_one.indicator (hlevel x)).mul measurable_const).aemeasurable

end CircleDomainRigidity

end

end OAI
