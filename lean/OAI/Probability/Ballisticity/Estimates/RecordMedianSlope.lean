import Mathlib
import OAI.Probability.Ballisticity.Estimates.MedianAeConst
import OAI.Probability.Ballisticity.Geometry.NormHeightPolygon

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def recordMedianSlope {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d) (a : ℝ) : ℝ :=
  (recordMedian ν ℓ hp f ⌊fluctuationScale (independentConditionedPairLaw ν ℓ)
    (commonIncrementProcess ℓ f 0) a⌋₊ : ℝ) /
      ⌊fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) a⌋₊

lemma recordFluctuationScale_tendsto {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    Tendsto (fun i => fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i)) atTop atTop := by
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ hp
  have hi := independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
    htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  exact (fluctuationScale_tendsto _ _ (measurable_commonIncrementProcess ℓ f 0) hi hne).comp hr

theorem recordMedian_linearization {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans)
    ∀ᶠ i in atTop, ∀ h : ℕ,
      (h:ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) (r i) →
      |((recordMedian ν (realPosition (step e)) hp f h:ℝ)-
        (h:ℝ)*recordMedianSlope ν (realPosition (step e)) hp f (r i))/r i| < ε := by
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  exact height_center_linearization (fun h => (recordMedian ν ℓ hp f h:ℝ))
    (by simp [recordMedian_zero]) r _ (recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1)
    (fun T ε hε => recordMedian_additive_uniform ν hue e f hef htrans r hr T hε) T hε

lemma recordMedianSlope_small {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) :
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans)
    Tendsto (fun i => recordMedianSlope ν (realPosition (step e)) hp f (r i)/r i) atTop (𝓝 0) := by
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  apply height_center_slope_small (fun h => (recordMedian ν ℓ hp f h:ℝ)) r _ hr.1
    (recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1)
  intro ε hε
  simpa only [one_mul, recordMedianSlope] using recordMedian_linearization ν hue e f hef htrans r hr 1 hε

theorem transverse_firstHit_linear_path_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans)
    letI : IsProbabilityMeasure (conditionedLaw ν (realPosition (step e))) :=
      conditionedLaw_probability ν _ hp
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i X => heightPolygon
        (fun h => signedCoordinate f (recordIndexPosition (realPosition (step e)) h X)-
          (h:ℝ)*recordMedianSlope ν (realPosition (step e)) hp f (r i)) (r i)
        (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T)
        atTop id (fun _ => conditionedLaw ν (realPosition (step e))) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
          gaussianPathFiniteLaw (T/(2*commonMeanWidth ν (realPosition (step e)))) I := by
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ hp
  obtain ⟨W,hW,hWf⟩ := transverse_firstHit_single_path_limit ν hue e f hef htrans r hr hT
  refine ⟨W,?_,hWf⟩
  apply height_path_change_center μ _ (fun h =>
    (measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ h))
      (fun h => (recordMedian ν ℓ hp f h:ℝ)) _ r _
      (recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1) T hT _ W hW
  exact fun ε hε => recordMedian_linearization ν hue e f hef htrans r hr (T+1) hε

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
