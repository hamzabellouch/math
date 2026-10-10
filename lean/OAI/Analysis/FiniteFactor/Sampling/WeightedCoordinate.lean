import OAI.Analysis.FiniteFactor.OrbitSampling.Measures
import Mathlib.Probability.Independence.Integration

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
noncomputable section

/-- Exact relative mass of a tail-coordinate event under a prefix product
weight. This includes zero-mass weights and requires no division by mass. -/
theorem weighted_prefix_coordinate_mass {ι : Type*} [DecidableEq ι]
    (μi : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μi i)]
    (J : Finset ι) (F : ι → ℝ → ℝ≥0∞) (hF : ∀ j, Measurable (F j))
    (i : ι) (hi : i ∉ J) (E : Set ℝ) (hE : MeasurableSet E) :
    ((Measure.infinitePi μi).withDensity (fun x => ∏ j ∈ J, F j (x j))) {x | x i ∈ E} =
      ((Measure.infinitePi μi).withDensity (fun x => ∏ j ∈ J, F j (x j))) Set.univ * μi i E := by
  classical
  let μ := Measure.infinitePi μi
  let W := fun x : ι → ℝ => ∏ j ∈ J, F j (x j)
  let B := fun x : ι → ℝ => E.indicator (fun _ => (1 : ℝ≥0∞)) (x i)
  let G := fun j : ι => if j = i then E.indicator (fun _ => (1 : ℝ≥0∞)) else F j
  have hG (j : ι) : Measurable (G j) := by
    dsimp [G]
    split_ifs
    · exact measurable_const.indicator hE
    · exact hF j
  have hind : iIndepFun (fun j (x : ι → ℝ) => G j (x j)) μ := iIndepFun_infinitePi hG
  have hproduct : (∏ j ∈ J, (fun x : ι → ℝ => G j (x j))) = W := by
    funext x
    simp only [Finset.prod_apply]
    apply prod_congr rfl
    intro j hj
    simp only [G,ite_eq_right (ne_of_mem_of_not_mem hj hi)]
  have heval : (fun x : ι → ℝ => G i (x i)) = B := by funext x; simp [G,B]
  have hind' := hind.indepFun_finsetProd_of_notMem (fun j => (hG j).comp (measurable_pi_apply j)) hi
  rw [hproduct,heval] at hind'
  have hW : Measurable W := Finset.measurable_prod J (fun j hj => (hF j).comp (measurable_pi_apply j))
  have hB : Measurable B := (measurable_const.indicator hE).comp (measurable_pi_apply i)
  have hEpre : MeasurableSet {x : ι → ℝ | x i ∈ E} := hE.preimage (measurable_pi_apply i)
  have hfub := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hW hB hind'
  have hcoord : (∫⁻ x, B x ∂μ) = μi i E := by
    rw [show B = {x : ι → ℝ | x i ∈ E}.indicator (fun _ => (1 : ℝ≥0∞)) by
      funext x; simp [B,Set.indicator]]
    rw [lintegral_indicator hEpre]
    simp only [lintegral_const,one_mul,Measure.restrict_apply_univ]
    have hh := congrArg (fun ν : Measure ℝ => ν E) (Measure.infinitePi_map_eval μi i)
    rw [Measure.map_apply (measurable_pi_apply i) hE] at hh
    exact hh
  rw [hcoord] at hfub
  rw [withDensity_apply _ hEpre,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,← lintegral_indicator hEpre]
  have he : {x : ι → ℝ | x i ∈ E}.indicator W = W*B := by
    funext x
    by_cases hx : x i ∈ E <;> simp [W,B,Set.indicator,hx]
  change (∫⁻ x, ({x : ι → ℝ | x i ∈ E}.indicator W) x ∂μ) = _
  rw [he]
  exact hfub

/-- The source sampling summand has exactly the Haar tail-coordinate
probability multiplied by its own mass. -/
theorem sourceSampling_tail_coordinate_mass (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (i : SourceCoordinate) (hi : s < i.1)
    (E : Set ℝ) (hE : MeasurableSet E) :
    sourceSamplingWeightedMeasure I s θ n {x | x i ∈ E} =
      sourceSamplingWeightedMeasure I s θ n Set.univ * unitIntervalMeasure E := by
  let F := fun j : SourceCoordinate => fun t : ℝ => ENNReal.ofReal
    (samplingWeight (decide (j ∈ I)) (sourceSamplingWidth s) (sourceSamplingCutoff s)
      t (Int.fract ((n : ℝ)*θ j)))
  have hF (j : SourceCoordinate) : Measurable (F j) := by
    apply Measurable.ennreal_ofReal
    exact (samplingWeight_measurable _ _ _).comp (measurable_id.prodMk measurable_const)
  have he : (fun x => ENNReal.ofReal (sourceSamplingWeight I s θ n x)) =
      (fun x => ∏ j ∈ sourceSamplingPrefix s, F j (x j)) := by
    funext x
    exact ENNReal.ofReal_prod_of_nonneg (fun j hj => (sourceSampling_weight_bound s _ _ _).1)
  rw [sourceSamplingWeightedMeasure,he]
  apply weighted_prefix_coordinate_mass _ _ F hF i _ E hE
  rw [sourceSamplingPrefix,CouplingParameters.mem_blockPrefix]
  omega

end
end FiniteFactor

end OAI
