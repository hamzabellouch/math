import OAI.Probability.SLE.Multipoint.MultipointLogClockTransport
import OAI.Probability.SLE.Multipoint.MultipointGlobalDiscount

namespace OAI

/-! The raw active costs and their bounds on individual completion
intervals. Disjoint active intervals contribute zero pair cost. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

def actualSingleCost (κ β a U : ℝ) (B : ℝ≥0 → ℝ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  regulator β U (logFactorClock κ (logLoewnerCoordinates G z t)-a)*
    logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal)^2

def actualPairCost (κ β az aw Uz Uw : ℝ) (B : ℝ≥0 → ℝ)
    (G : ℝ≥0 → ℂ → ℂ) (z w : ℂ) (t : ℝ) : ℝ :=
  (regulator β Uz (logFactorClock κ (logLoewnerCoordinates G z t)-az)*
    regulator β Uw (logFactorClock κ (logLoewnerCoordinates G w t)-aw))^(-exponent (greenExponent κ))*
      (logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal)*
        logVelocity κ (logLoewnerCoordinates G w t) (B t.toNNReal))

lemma actualSingleCost_nonneg (κ β a U : ℝ) (B : ℝ≥0 → ℝ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ) : 0 ≤ actualSingleCost κ β a U B G z t :=
  mul_nonneg (regulator_pos _ _ _).le (sq_nonneg _)

lemma actualPairCost_nonneg (κ β az aw Uz Uw : ℝ) (B : ℝ≥0 → ℝ)
    (G : ℝ≥0 → ℂ → ℂ) (z w : ℂ) (t : ℝ) :
    0 ≤ actualPairCost κ β az aw Uz Uw B G z w t :=
  mul_nonneg (Real.rpow_nonneg (mul_pos (regulator_pos _ _ _) (regulator_pos _ _ _)).le _)
    (mul_pos (logVelocity_pos _ _ _) (logVelocity_pos _ _ _)).le

theorem actualSingleCost_bound
    {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → ℝ} (hB : Continuous B)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t) γ G F)
    (σ T : ℝ≥0) (hσT : σ ≤ T) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (β a U : ℝ) (hβ : 0 < β) (hU : 0 ≤ U)
    (hstart : σ < T → logFactorClock κ (logLoewnerCoordinates G z σ) = a)
    (hend : σ < T → logFactorClock κ (logLoewnerCoordinates G z T)-a ≤ U) :
    IntervalIntegrable (actualSingleCost κ β a U B G z) volume (σ : ℝ) (T : ℝ) ∧
      (∫ t in (σ : ℝ)..(T : ℝ), actualSingleCost κ β a U B G z t) ≤ 2/(κ*β) := by
  rcases lt_or_eq_of_le hσT with hlt | rfl
  · have he : actualSingleCost κ β a U B G z = fun t =>
        regulator β U (logFactorClock κ (logLoewnerCoordinates G z t)-
          logFactorClock κ (logLoewnerCoordinates G z σ))*
          logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal)^2 := by
      funext t
      rw [actualSingleCost, hstart hlt]
    rw [he]
    refine ⟨hw.logFactor_single_intervalIntegrable hB σ T hσT z hz β U,
      hw.logFactor_single_regulator_integral_le hκ hB σ T hσT z hz hβ hU ?_⟩
    simpa only [hstart hlt] using hend hlt
  · exact ⟨by simp, by simp only [intervalIntegral.integral_same]; positivity⟩

def overlapStart (σz σw : ℝ≥0) : ℝ≥0 := max σz σw

def overlapEnd (σz σw Tz Tw : ℝ≥0) : ℝ≥0 := max (overlapStart σz σw) (min Tz Tw)

theorem actualPairCost_bound
    {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → ℝ} (hB : Continuous B)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t) γ G F)
    (hgrowth : PublishedDiskUnivalentGrowth) (J : ℂ → ℂ)
    (hJ : DifferentiableOn ℂ J upperHalfPlane) (hJinj : InjOn J upperHalfPlane)
    (σz σw Tz Tw : ℝ≥0) (z w : ℂ)
    (hz : z ∈ survivingDomain γ Tz) (hw' : w ∈ survivingDomain γ Tw) (hne : z ≠ w)
    (β az aw Uz Uw : ℝ) (hβ : 0 ≤ β) (hM : 0 ≤ exponent (greenExponent κ))
    (hdecay : 2*(exponent (greenExponent κ)*β) < 2/κ)
    (hstartz : σz < Tz → logFactorClock κ (logLoewnerCoordinates G z σz) = az)
    (hstartw : σw < Tw → logFactorClock κ (logLoewnerCoordinates G w σw) = aw)
    (hgeoz : σz < Tz → σw < Tw → physicalConformalRadius J G σz z ≤ dist (J z) (J w))
    (hgeow : σz < Tz → σw < Tw → physicalConformalRadius J G σw w ≤ dist (J z) (J w)) :
    IntervalIntegrable (actualPairCost κ β az aw Uz Uw B G z w) volume
      (overlapStart σz σw : ℝ) (overlapEnd σz σw Tz Tw : ℝ) ∧
      (∫ t in (overlapStart σz σw : ℝ)..(overlapEnd σz σw Tz Tw : ℝ),
        actualPairCost κ β az aw Uz Uw B G z w t) ≤
          interactionBudget 2 (exponent (greenExponent κ)*(κ*β)) := by
  have hadm : 2*(exponent (greenExponent κ)*(κ*β)) < 2 := by
    have hh := (source_pair_exponent_admissible (c := exponent (greenExponent κ)*β) hκ).mpr hdecay
    convert hh using 1
    ring
  by_cases ht : overlapStart σz σw < min Tz Tw
  · have hzt : σz < Tz := (le_max_left σz σw).trans_lt (ht.trans_le (min_le_left _ _))
    have hwt : σw < Tw := (le_max_right σz σw).trans_lt (ht.trans_le (min_le_right _ _))
    have he : actualPairCost κ β az aw Uz Uw B G z w = fun t =>
        (regulator β Uz (logFactorClock κ (logLoewnerCoordinates G z t)-
          logFactorClock κ (logLoewnerCoordinates G z σz))*
         regulator β Uw (logFactorClock κ (logLoewnerCoordinates G w t)-
          logFactorClock κ (logLoewnerCoordinates G w σw)))^(-exponent (greenExponent κ))*
         (logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal)*
          logVelocity κ (logLoewnerCoordinates G w t) (B t.toNNReal)) := by
      funext t
      rw [actualPairCost, hstartz hzt, hstartw hwt]
    rw [he, overlapEnd, max_eq_right ht.le]
    have hzl := survivingDomain_antitone γ (min_le_left Tz Tw) hz
    have hwl := survivingDomain_antitone γ (min_le_right Tz Tw) hw'
    exact ⟨hw.logFactor_pair_intervalIntegrable hB σz σw (overlapStart σz σw) (min Tz Tw)
        (le_max_left _ _) (le_max_right _ _) ht.le z w hzl hwl β _ Uz Uw,
      hw.logFactor_pair_regulator_integral_le hκ hB hgrowth J hJ hJinj σz σw
        (overlapStart σz σw) (min Tz Tw) (le_max_left _ _) (le_max_right _ _) ht.le
        z w hzl hwl hne (hgeoz hzt hwt) (hgeow hzt hwt) hβ hM hdecay Uz Uw⟩
  · have he : overlapEnd σz σw Tz Tw = overlapStart σz σw :=
      max_eq_left (le_of_not_gt ht)
    rw [he]
    exact ⟨by simp, by simpa only [intervalIntegral.integral_same] using
      (interactionBudget_pos (by norm_num : (0 : ℝ) < 2) hadm).le⟩

end SLEExactGauge.Multipoint

end

end OAI
