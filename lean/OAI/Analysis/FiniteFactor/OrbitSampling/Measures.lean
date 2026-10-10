import OAI.Analysis.FiniteFactor.OrbitSampling.Weights

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

abbrev sourceSamplingHaar : Measure (SourceCoordinate → ℝ) :=
  Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)

def sourceSamplingWeightedMeasure (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) : Measure (SourceCoordinate → ℝ) :=
  sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (sourceSamplingWeight I s θ n x))

instance sourceSamplingWeightedMeasure_finite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) : IsFiniteMeasure (sourceSamplingWeightedMeasure I s θ n) := by
  apply isFiniteMeasure_withDensity
  let C := ((sourceBlockSize s : ℝ)^(13/5 : ℝ))^(sourceSamplingPrefix s).card
  have hh : (∫⁻ x, ENNReal.ofReal (sourceSamplingWeight I s θ n x) ∂sourceSamplingHaar) ≤ ENNReal.ofReal C := by
    calc
      _ ≤ ∫⁻ _x, ENNReal.ofReal C ∂sourceSamplingHaar :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (sourceSamplingWeight_bounds I s θ n x).2)
      _ = _ := by simp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh

def sourceSamplingSummand (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    Measure ((SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) :=
  (sourceSamplingWeightedMeasure I s θ n).map (fun x => (x,coordinateRotate θ n x))

instance sourceSamplingSummand_finite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) : IsFiniteMeasure (sourceSamplingSummand I s θ n) := by
  unfold sourceSamplingSummand
  infer_instance

theorem sourceSamplingSummand_first_marginal (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    (sourceSamplingSummand I s θ n).map Prod.fst = sourceSamplingWeightedMeasure I s θ n := by
  unfold sourceSamplingSummand
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x,coordinateRotate θ n x)) :=
    measurable_id.prodMk (coordinateRotate_preserving θ n).measurable
  rw [Measure.map_map measurable_fst hp]
  exact Measure.map_id

/-- Finite positive untrimmed measures averaged over the constructed powers.
No weak limit or uniform marginal bound is asserted by this definition. -/
def sourceSamplingUntrimmed (I : Finset SourceCoordinate) (s : ℕ) (θ : SourceCoordinate → ℝ) :
    Measure ((SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) :=
  ENNReal.ofReal (1/((sourceSamplingPowers s).card : ℝ)) •
    ∑ n ∈ sourceSamplingPowers s, sourceSamplingSummand I s θ n

theorem sourceSamplingHaar_cube : ∀ᵐ x ∂sourceSamplingHaar,
    ∀ i : SourceCoordinate, x i ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  have hh : ∀ᵐ t ∂sourceSamplingHaar.map (fun x => x i), t ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Measure.infinitePi_map_eval]
    exact ae_restrict_mem measurableSet_Ico
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ico).mp hh

/-- The weighted source law already orders every coordinate in its prefix. -/
theorem sourceSamplingWeightedMeasure_orders (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    ∀ᵐ x ∂sourceSamplingWeightedMeasure I s θ n,
      ∀ i ∈ sourceSamplingPrefix s, x i < coordinateRotate θ n x i := by
  rw [sourceSamplingWeightedMeasure,ae_withDensity_iff
    ((sourceSamplingWeight_measurable I s θ n).ennreal_ofReal)]
  filter_upwards [sourceSamplingHaar_cube] with x hx hw
  have hw' : sourceSamplingWeight I s θ n x ≠ 0 := by
    intro he
    exact hw (by rw [he]; simp)
  exact sourceSamplingWeight_orders_prefix I s θ n x hx hw'

end
end FiniteFactor

end OAI
