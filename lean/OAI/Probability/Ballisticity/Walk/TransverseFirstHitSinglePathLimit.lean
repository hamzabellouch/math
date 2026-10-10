import Mathlib
import OAI.Probability.Ballisticity.Walk.GaussianPathFiniteLawSmul

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
namespace DirectionalTransience

theorem transverse_firstHit_single_path_limit {d : ℕ} (ν : Measure (Row d))
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
          (recordMedian ν (realPosition (step e)) hp f h : ℝ)) (r i)
        (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T)
        atTop id (fun _ => conditionedLaw ν (realPosition (step e))) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
          gaussianPathFiniteLaw (T/(2*commonMeanWidth ν (realPosition (step e)))) I := by
  let ℓ := realPosition (step e)
  let μ := conditionedLaw ν ℓ
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ hp
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ hp
  let F := fun h X => signedCoordinate f (recordIndexPosition ℓ h X)
  have hF (h : ℕ) : Measurable (F h) :=
    (measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ h)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  have hi := independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
    htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto _ _
    (measurable_commonIncrementProcess ℓ f 0) hi hne).comp hr.1
  apply height_median_path_limit μ F hF (fun h => (recordMedian ν ℓ hp f h : ℝ))
    (recordMedian_spec ν ℓ hp f) r n (fun _ => fluctuationScale_nonneg _ _ _)
    hn (commonMeanWidth ν ℓ) _ hT
  intro S hS
  obtain ⟨W,hW,hWf⟩ := transverse_firstHit_path_limit ν hue e f hef htrans r hr hS
  refine ⟨W,?_,hWf⟩
  have h0 : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, firstHitPairGap ℓ f 0 P = 0 := by
    have hx := (conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν)
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hx,
      Measure.quasiMeasurePreserving_snd.ae hx] with P hP1 hP2
    simp [firstHitPairGap,recordIndexPosition,recordIndexTime_zero,hP1,hP2]
  have he (i : ℕ) : ((heightPathLaw μ F hF (r i) (n i) S).prod
      (heightPathLaw μ F hF (r i) (n i) S)).map
        (fun paths => paths.1 - paths.2) =
      (⟨(independentConditionedPairLaw ν ℓ).map (fun P => scaledPolygon
          (heightIncrement (fun h => firstHitPairGap ℓ f h P)) (r i) (n i) S),
        inferInstance⟩ : ProbabilityMeasure C(unitInterval,ℝ)) := by
    apply Subtype.ext
    change ((heightPathLaw μ F hF (r i) (n i) S : Measure C(unitInterval,ℝ)).prod
      (heightPathLaw μ F hF (r i) (n i) S : Measure C(unitInterval,ℝ))).map
      (fun p => p.1-p.2) = _
    rw [heightPathLaw_iid_difference]
    apply Measure.map_congr
    filter_upwards [h0] with P hP
    change heightPolygon (fun h => firstHitPairGap ℓ f h P) (r i) (n i) S = _
    simp [heightPolygon,hP]
  have hId : (⟨(W : Measure C(unitInterval,ℝ)).map id,
      inferInstance⟩ : ProbabilityMeasure C(unitInterval,ℝ)) = W := by
    apply Subtype.ext
    exact Measure.map_id
  have h := hW.tendsto
  rw [hId] at h
  simpa only [he] using h

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

end
end

end OAI
