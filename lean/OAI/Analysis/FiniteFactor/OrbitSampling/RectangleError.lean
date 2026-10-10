import OAI.Analysis.FiniteFactor.OrbitSampling.RationalTests

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- The elementary probability-space Cauchy--Schwarz bound, proved by
integrating the nonnegative square centered at the mean. -/
theorem sampling_integral_square_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, f x^2 ∂μ := by
  let c := ∫ x, f x ∂μ
  have he : (fun x => (f x-c)^2) = (fun x => f x^2-2*c*f x+c^2) := by funext x; ring
  have hh : 0 ≤ ∫ x, (f x-c)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hi : Integrable (fun x => f x^2-2*c*f x) μ := hf2.sub (hf.const_mul (2*c))
  have hc : Integrable (fun _x : Ω => c^2) μ := integrable_const _
  rw [he,integral_add hi hc,integral_sub hf2 (hf.const_mul (2*c)),integral_const_mul] at hh
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at hh
  change c^2 ≤ _
  change 0 ≤ (∫ x, f x^2 ∂μ)-2*c*c+c^2 at hh
  nlinarith

/-- Actual rectangle mass equals the integral of the first tested empirical
density at every admissible stage. -/
theorem sourceSamplingUntrimmed_rectangle_mass (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ : SourceCoordinate → ℝ) :
    ((sourceSamplingUntrimmed I stage θ) (sourceSamplingRectangle E G)).toReal =
      ∫ x, sourceSamplingEmpiricalDensity stage false (fun i => decide (i ∈ I)) E G θ x
        ∂sourceSamplingHaar := by
  let z := sourceSamplingEmpiricalDensity stage false (fun i => decide (i ∈ I)) E G θ
  have hm := sourceSamplingEmpiricalDensity_measurable stage false (fun i => decide (i ∈ I)) E G hE hG θ
  have hb := sourceSamplingEmpiricalDensity_bounds stage false (fun i => decide (i ∈ I)) E G θ
  have hi : Integrable z sourceSamplingHaar :=
    sampling_integrable_bounded sourceSamplingHaar z hm _ (fun x => by
      rw [abs_of_nonneg (hb x).1]; exact (hb x).2)
  have hh := congrArg (fun ν : Measure (SourceCoordinate → ℝ) => ν Set.univ)
    (sourceSamplingUntrimmed_tested_marginal I stage false E G hE hG houtside θ)
  rw [Measure.map_apply (sourceSamplingEndpoint_measurable false) MeasurableSet.univ,
    Set.preimage_univ,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  rw [hh,← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => (hb x).1)),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => (hb x).1))]

/-- Full squared sampling error bounds the squared discrepancy of the actual
rectangle mass and the ideal product integral. -/
theorem sourceSamplingUntrimmed_rectangle_error (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ : SourceCoordinate → ℝ) :
    (((sourceSamplingUntrimmed I stage θ) (sourceSamplingRectangle E G)).toReal -
      ∫ x, sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I)) E G x ∂sourceSamplingHaar)^2 ≤
    sourceSamplingSquaredError stage false (fun i => decide (i ∈ I)) E G θ := by
  rw [sourceSamplingUntrimmed_rectangle_mass I stage E G hE hG houtside θ]
  let z := sourceSamplingEmpiricalDensity stage false (fun i => decide (i ∈ I)) E G θ
  let g := sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I)) E G
  let C := (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card
  have hzm := sourceSamplingEmpiricalDensity_measurable stage false (fun i => decide (i ∈ I)) E G hE hG θ
  have hgm := sourceSamplingIdealDensity_measurable stage false (fun i => decide (i ∈ I)) E G hE hG
  have hzb := sourceSamplingEmpiricalDensity_bounds stage false (fun i => decide (i ∈ I)) E G θ
  have hgb := sourceSamplingIdealDensity_bounds stage false (fun i => decide (i ∈ I)) E G hE hG
  have hzi : Integrable z sourceSamplingHaar := sampling_integrable_bounded sourceSamplingHaar z hzm C
    (fun x => by rw [abs_of_nonneg (hzb x).1]; exact (hzb x).2)
  have hgi : Integrable g sourceSamplingHaar := sampling_integrable_bounded sourceSamplingHaar g hgm C
    (fun x => by rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2)
  have hei : Integrable (fun x => (z x-g x)^2) sourceSamplingHaar := by
    apply sampling_integrable_bounded sourceSamplingHaar _ ((hzm.sub hgm).pow_const 2) (C^2)
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hz' : 0 ≤ z x ∧ z x ≤ C := hzb x
    have hg' : 0 ≤ g x ∧ g x ≤ C := hgb x
    change (z x-g x)^2 ≤ C^2
    nlinarith [sq_nonneg (z x+g x),mul_nonneg (show 0 ≤ C-(z x-g x) by linarith)
      (show 0 ≤ C+(z x-g x) by linarith)]
  have hh := sampling_integral_square_le sourceSamplingHaar (fun x => z x-g x) (hzi.sub hgi) hei
  rw [integral_sub hzi hgi] at hh
  exact hh

end
end FiniteFactor

end OAI
