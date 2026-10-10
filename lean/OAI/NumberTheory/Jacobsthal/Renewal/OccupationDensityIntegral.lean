import OAI.NumberTheory.Jacobsthal.Primes.PrimeOccupationDensity

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.OccupationDensityIntegral

open _root_.Set _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures InvariantInverseWeights
open CompactInverseTest CompactLogOccupationTest PrimeOccupationDensity
open CycleResponse AdmissibleCycleTests NormalizedOccupationLimit OccupationConstant
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.InvariantCostBound

noncomputable def rawTest (H : Side → ℝ×ℝ → ℝ) (x : ℝ×State) : ℝ :=
  H (stateSide x.2) (Real.exp x.1,stateRatio x.2)

theorem density_mul_raw (ell : ℝ) (H : Side → ℝ×ℝ → ℝ) (x : ℝ×State) :
    density ell x*rawTest H x = arrivalTest ell H x/costMass := by
  classical
  by_cases h : stateRatio x.2 < Real.exp x.1/ell
  · change (if stateRatio x.2 < Real.exp x.1/ell then (Real.exp x.1)^2/(stateWeight x.2*costMass) else 0)*rawTest H x =
      (if stateRatio x.2 < Real.exp x.1/ell then logTest H x else 0)/costMass
    rw [ite_eq_left h,ite_eq_left h]
    unfold logTest
    rw [inverseTest_eq (stateRatio_valid x.2),← SuccessfulRewardComparison.stateWeight_eq]
    unfold rawTest
    ring
  · simp [density,arrivalTest,AdmissibleCycleTests.mask,h]

theorem compactBound_product_integrable {F : Test} (hF : Measurable F) (hB : HasCompactBound F) :
    Integrable F baseMeasure := by
  obtain ⟨C,M,hC,hM,hbound,hsupport⟩ := hB
  let A : Set (ℝ×State) := Icc (-M) M ×ˢ univ
  have hA : MeasurableSet A := measurableSet_Icc.prod MeasurableSet.univ
  have hfin : baseMeasure A < ∞ := by
    rw [baseMeasure,Measure.prod_prod,Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top stateMeasure univ)
  let : IsFiniteMeasure (baseMeasure.restrict A) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hdom : Integrable (A.indicator (fun _ => C)) baseMeasure :=
    (integrable_indicator_iff hA).mpr (integrable_const C)
  apply hdom.mono' hF.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx]
    exact hbound x
  · have hlarge : M < |x.1| := by
      apply lt_of_not_ge
      intro hh
      exact hx ⟨abs_le.mp hh,Set.mem_univ _⟩
    rw [hsupport x hlarge, norm_zero,indicator_of_notMem hx]

theorem rawTest_integrable {H : Side → ℝ×ℝ → ℝ} (ell : ℝ)
    (hF : Measurable (arrivalTest ell H)) (hB : HasCompactBound (arrivalTest ell H)) :
    Integrable (rawTest H) (limitingMeasure ell) := by
  have hI := compactBound_product_integrable hF hB
  have hD : Measurable (fun x => ENNReal.ofReal (density ell x)) := ENNReal.measurable_ofReal.comp (density_measurable ell)
  have htop : ∀ᵐ x ∂baseMeasure,ENNReal.ofReal (density ell x) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  apply (integrable_withDensity_iff_integrable_smul' hD htop).mpr
  have he : (fun x => (ENNReal.ofReal (density ell x)).toReal • rawTest H x) =
      (fun x => arrivalTest ell H x/costMass) := by
    funext x
    rw [ENNReal.toReal_ofReal (density_nonneg ell x),smul_eq_mul,density_mul_raw]
  rw [he]
  exact hI.div_const costMass

theorem limiting_integral_eq_invariant {H : Side → ℝ×ℝ → ℝ} (ell : ℝ)
    (hF : Measurable (arrivalTest ell H)) (hB : HasCompactBound (arrivalTest ell H)) :
    (∫ x,rawTest H x ∂limitingMeasure ell) = invariantAverage (arrivalTest ell H) := by
  have hI := compactBound_product_integrable hF hB
  have hD : Measurable (fun x => ENNReal.ofReal (density ell x)) := ENNReal.measurable_ofReal.comp (density_measurable ell)
  have htop : ∀ᵐ x ∂baseMeasure,ENNReal.ofReal (density ell x) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [limitingMeasure,integral_withDensity_eq_integral_toReal_smul hD htop]
  have he : (fun x => (ENNReal.ofReal (density ell x)).toReal • rawTest H x) =
      (fun x => arrivalTest ell H x/costMass) := by
    funext x
    rw [ENNReal.toReal_ofReal (density_nonneg ell x),smul_eq_mul,density_mul_raw]
  rw [he,integral_div]
  have hfubini := integral_prod_symm (arrivalTest ell H) hI
  change (∫ x,arrivalTest ell H x ∂baseMeasure)/costMass = _
  rw [baseMeasure,hfubini]
  rfl

theorem continuous_test_density {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 0 < ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) :
    Integrable (rawTest H) (limitingMeasure ell) ∧
      (∫ x,rawTest H x ∂limitingMeasure ell) = invariantAverage (arrivalTest ell H) := by
  have htest := arrivalTest_admissible hH hcompact ha hb hell hsupport
  exact ⟨rawTest_integrable ell htest.measurable htest.compactBound,
    limiting_integral_eq_invariant ell htest.measurable htest.compactBound⟩

end NumberTheoryLean.OccupationDensityIntegral

end

end Erdos970

end OAI
