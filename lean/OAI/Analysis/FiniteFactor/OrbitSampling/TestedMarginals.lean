import OAI.Analysis.FiniteFactor.OrbitSampling.TestedTransport

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

def sourceSamplingEndpoint (r : Bool)
    (p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) : SourceCoordinate → ℝ :=
  if r then p.2 else p.1

theorem sourceSamplingEndpoint_measurable (r : Bool) : Measurable (sourceSamplingEndpoint r) := by
  cases r
  · exact measurable_fst
  · exact measurable_snd

/-- Both actual rectangle-restricted marginal measures for a single power. -/
theorem sourceSamplingSummand_tested_marginal (I : Finset SourceCoordinate) (stage : ℕ)
    (r : Bool) (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    ((sourceSamplingSummand I stage θ n).restrict (sourceSamplingRectangle E G)).map
        (sourceSamplingEndpoint r) =
      sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingProduct stage r (fun i => decide (i ∈ I)) E G n θ x)) := by
  rw [sourceSamplingSummand_restrict_rectangle I stage E G hE hG houtside θ n]
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x,coordinateRotate θ n x)) :=
    measurable_id.prodMk (coordinateRotate_preserving θ n).measurable
  rw [Measure.map_map (sourceSamplingEndpoint_measurable r) hp]
  cases r
  · exact Measure.map_id
  · change (sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingProduct stage false (fun i => decide (i ∈ I)) E G n θ x))).map
      (coordinateRotate θ n) = _
    have hw : Measurable (fun x => ENNReal.ofReal
        (sourceSamplingProduct stage false (fun i => decide (i ∈ I)) E G n θ x)) :=
      (((sourceSamplingProduct_measurable stage false (fun i => decide (i ∈ I)) E G hE hG n).comp
        (measurable_const.prodMk measurable_id)).ennreal_ofReal)
    rw [sourceSamplingHaar_rotate_withDensity θ n _ hw]
    apply withDensity_congr_ae
    filter_upwards [sourceSamplingHaar_cube] with y hy
    rw [sourceSamplingProduct_second_inverse I stage E G θ y n hy]

/-- Averaging commutes with rectangle restriction and either endpoint map.
The density is the previously estimated empirical function, exactly. -/
theorem sourceSamplingUntrimmed_tested_marginal (I : Finset SourceCoordinate) (stage : ℕ)
    (r : Bool) (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ : SourceCoordinate → ℝ) :
    ((sourceSamplingUntrimmed I stage θ).restrict (sourceSamplingRectangle E G)).map
        (sourceSamplingEndpoint r) =
      sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingEmpiricalDensity stage r (fun i => decide (i ∈ I)) E G θ x)) := by
  let S := sourceSamplingPowers stage
  let c : ℝ≥0∞ := ENNReal.ofReal (1/((sourceSamplingPowers stage).card : ℝ))
  let w := fun n => sourceSamplingProduct stage r (fun i => decide (i ∈ I)) E G n θ
  have hrep : (fun x => ENNReal.ofReal (sourceSamplingEmpiricalDensity stage r
      (fun i => decide (i ∈ I)) E G θ x)) =
      (fun x => c*∑ n ∈ S, ENNReal.ofReal (w n x)) := by
    funext x
    simp only [sourceSamplingEmpiricalDensity]
    rw [div_eq_mul_inv,mul_comm,← one_div,ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun n _ => (sourceSamplingProduct_bounds stage r
        (fun i => decide (i ∈ I)) E G n θ x).1)]
  rw [hrep]
  have hf := sourceSamplingEndpoint_measurable r
  have hR := sourceSamplingRectangle_measurable E G hE hG
  ext A hA
  rw [Measure.map_apply hf hA,Measure.restrict_apply (hf hA)]
  unfold sourceSamplingUntrimmed
  rw [Measure.smul_apply,Measure.finsetSum_apply,withDensity_apply _ hA]
  have hterm (n : ℤ) : sourceSamplingSummand I stage θ n
      (sourceSamplingEndpoint r ⁻¹' A ∩ sourceSamplingRectangle E G) =
      ∫⁻ x in A, ENNReal.ofReal (w n x) ∂sourceSamplingHaar := by
    rw [← Measure.restrict_apply (hf hA),← Measure.map_apply hf hA,
      sourceSamplingSummand_tested_marginal I stage r E G hE hG houtside θ n]
    exact withDensity_apply _ hA
  simp only [hterm,smul_eq_mul]
  rw [lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
  congr 1
  exact (lintegral_finsetSum S (fun n _ =>
    (((sourceSamplingProduct_measurable stage r (fun i => decide (i ∈ I)) E G hE hG n).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal))).symm

end
end FiniteFactor

end OAI
