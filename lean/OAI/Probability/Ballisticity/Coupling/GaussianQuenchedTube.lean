import Mathlib
import OAI.Probability.Ballisticity.Coupling.QuenchedGaussian
import OAI.Probability.Ballisticity.Renewal.PositiveQuenchedEvent
import OAI.Probability.Ballisticity.Geometry.HeightTubeWindow

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma quenched_median_test_concentration_of_law {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) (T : ℝ) (hT : 0 < T)
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (T/(2*commonMeanWidth ν (realPosition (step e)))) I)
    (x : Lattice d) (F : C(unitInterval,ℝ) →ᵇ ℝ) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    TendstoInMeasure (environmentLaw ν)
      (fun i => quenchedMedianPathTest ν ℓ hp f x (r i) (n i) T F) atTop
      (fun _ => ∫ g, F g ∂(W : Measure C(unitInterval,ℝ))) := by
  obtain ⟨W',hW',hh⟩ := actual_quenched_gaussian_path_tests ν hue e f hef htrans r hr T hT
  have he : W'=W := by
    apply Subtype.ext
    apply continuous_path_measure_ext (W' : Measure C(unitInterval,ℝ)) (W : Measure C(unitInterval,ℝ))
    intro I
    rw [hW' I,hW I]
  subst W'
  exact (hh x F).2

def medianTubeEndpoint {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d)
    (x : Lattice d) (H : ℕ) (L R : ℝ) : Set (Path d) :=
  {X | heightTubeEndpointEvent (fun j => signedCoordinate f
    (recordIndexPosition ℓ j (fun k => X k-x))-(recordMedian ν ℓ hp f j:ℝ)) H L R}

lemma measurableSet_medianTubeEndpoint {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d)
    (x : Lattice d) (H : ℕ) (L R : ℝ) : MeasurableSet (medianTubeEndpoint ν ℓ hp f x H L R) := by
  have hm (j : ℕ) : Measurable (fun X : Path d => signedCoordinate f
      (recordIndexPosition ℓ j (fun k => X k-x))-(recordMedian ν ℓ hp f j:ℝ)) :=
    (((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ j)).comp (by fun_prop)).sub_const _
  exact measurableSet_heightTubeEndpointEvent _ hm H L R

lemma quenched_gaussian_noDrop_tube_from_test {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (2/(2*commonMeanWidth ν (realPosition (step e)))) I)
    (ρ δ B : ℝ) (hδ : 0 < δ) (F : C(unitInterval,ℝ) →ᵇ ℝ)
    (hF : ∀ g, 0 ≤ F g ∧ F g ≤ 1)
    (hFs : ∀ g, F g ≠ 0 → ‖g‖ < B ∧ ∀ t : unitInterval,
      dist t (⟨(1:ℝ)/2,by norm_num,by norm_num⟩ : unitInterval) ≤ δ → |g t| < ρ)
    (hb : 0 < ∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (bStar : ℕ → ℝ) (hbStar : Tendsto bStar atTop atTop) (x : Lattice d) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    Tendsto (fun i => (environmentLaw ν).real {ω |
      (noDropQuenchedKernel ℓ x ω).real
        (medianTubeEndpoint ν ℓ hp f x ⌊n i⌋₊ (bStar i*r i) (ρ*r i)) <
          (∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))/2}) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let τ : unitInterval := ⟨(1:ℝ)/2,by norm_num,by norm_num⟩
  have hn : Tendsto n atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have ht' : Tendsto (fun i => dist (layerGridPoint (2*n i) ⌊n i⌋₊) τ) atTop (𝓝 0) := by
    simpa only [τ, dist_self] using (half_layer_grid_tendsto n hn).dist (tendsto_const_nhds (x := τ))
  have ht : ∀ᶠ i in atTop, dist (layerGridPoint (2*n i) ⌊n i⌋₊) τ ≤ δ :=
    (ht'.eventually_lt_const hδ).mono fun _ h => h.le
  have hlim := quenched_median_test_concentration_of_law ν hue e f hef htrans r hr 2 (by norm_num) W hW x F
  apply event_lower_mass_of_test_concentration (environmentLaw ν) _ _ _ hb hlim
  filter_upwards [hr.1.eventually_gt_atTop 0,hn.eventually_gt_atTop 0,
    hbStar.eventually_ge_atTop B,ht] with i hri hni hBi hti
  exact ae_of_all _ (fun ω => by
    apply integral_lower_test_le_event (noDropQuenchedKernel ℓ x ω) _
      (F.continuous.measurable.comp (measurable_medianFirstHitPath ν ℓ hp f x (r i) (n i) 2))
      (fun X => hF _) _ (measurableSet_medianTubeEndpoint ν ℓ hp f x _ _ _)
    intro X hX
    obtain ⟨hg,he⟩ := hFs _ hX
    exact heightPolygon_window_implies_tube _ _ _ hri hni B (bStar i) ρ δ hBi τ hg he hti)

end DirectionalTransience

end

end

end OAI
