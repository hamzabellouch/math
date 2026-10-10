import OAI.Probability.InvariantIsing.Pressure.VarianceLimit
import OAI.Probability.InvariantIsing.Core.FiniteGaussianVariance
import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi

namespace OAI

/-! The variance estimate passes from finite positive-mass leaf cutoffs to the
actual countable spin/cascade-leaf prior. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology NNReal

namespace InvariantIsing

theorem cylinder_cgf_variance_le_of_finite_restrictions {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (A : X → ℕ →₀ ℝ)
    {B C : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ)
    (hfinite : ∀ S : Set X, S.Finite → ν S ≠ 0 →
      variance (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g)
        (normalizedRestriction ν S) t) gaussianCoordinates ≤ C) :
    variance (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g) ν t)
      gaussianCoordinates ≤ C := by
  obtain ⟨S, hS, hpos, hExh⟩ := countable_reference_exhaustion ν
  let νn := fun n => normalizedRestriction ν (S n)
  have : ∀ n, IsProbabilityMeasure (νn n) := fun n => normalizedRestriction_probability (hpos n)
  let H := fun p : (ℕ → ℝ) × X => t * cylinderField (A p.2) p.1
  have hH : Measurable H := (measurable_cylinderFields A).const_mul t
  have hLaw (x : X) : gaussianCoordinates.map (fun g => H (g, x)) =
      gaussianReal 0 (⟨t ^ 2, sq_nonneg t⟩ * (((A x).sum (fun _ c => c ^ 2)).toNNReal)) :=
    cylinder_scaled_law A x t
  have hVar (x : X) :
      ((⟨t ^ 2, sq_nonneg t⟩ : ℝ≥0) * (((A x).sum (fun _ c => c ^ 2)).toNNReal) : ℝ) ≤ t ^ 2 * B := by
    change t ^ 2 * (((A x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ _
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c ^ 2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg t)
  let f := fun n g => Real.log (∫ x, Real.exp (H (g, x)) ∂νn n)
  let F := fun g => Real.log (∫ x, Real.exp (H (g, x)) ∂ν)
  have hfm (n : ℕ) : Measurable (f n) :=
    hH.exp.stronglyMeasurable.integral_prod_right'.measurable.log
  have hFm : Measurable F := hH.exp.stronglyMeasurable.integral_prod_right'.measurable.log
  have hf (n : ℕ) : MemLp (f n) 2 gaussianCoordinates :=
    (memLp_two_iff_integrable_sq (hfm n).aestronglyMeasurable).mpr
      (gaussian_log_partition_second (ν := νn n) hH hLaw hVar).1
  have hF : MemLp F 2 gaussianCoordinates :=
    (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).mpr
      (gaussian_log_partition_second (ν := ν) hH hLaw hVar).1
  have hm : Tendsto (fun n => ∫ g, f n g ∂gaussianCoordinates) atTop
      (𝓝 (∫ g, F g ∂gaussianCoordinates)) :=
    gaussian_log_restriction_expectation_tendsto hH hLaw hVar
      (fun n => (hS n).measurableSet) hExh hpos
  have he := (gaussian_field_exp_integrable (ν := ν) hH hLaw hVar 1).1
  simp only [one_mul] at he
  have ht : ∀ᵐ g ∂gaussianCoordinates, Tendsto (fun n => f n g) atTop (𝓝 (F g)) := by
    filter_upwards [he.prod_right_ae] with g hg
    have hz : 0 < ∫ x, Real.exp (H (g, x)) ∂ν := MeasureTheory.integral_exp_pos hg
    exact (Real.continuousAt_log hz.ne').tendsto.comp
      (normalized_restriction_integral_tendsto (fun n => (hS n).measurableSet) hExh hg)
  have hv (n : ℕ) : variance (f n) gaussianCoordinates ≤ C :=
    hfinite (S n) (hS n) (hpos n)
  exact variance_le_of_ae_tendsto_of_mean_tendsto hf hF ht hm hv

/-- The countable spin/leaf Gaussian log partition inherits the uniform
coefficient variance bound from the finite-dimensional Gaussian
Poincaré inequality. -/
theorem countable_cylinder_cgf_variance_le (hpub : GaussianLipschitzVarianceInput)
    {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (A : X → ℕ →₀ ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) :
    variance (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g) ν t)
      gaussianCoordinates ≤ t ^ 2 * B := by
  apply cylinder_cgf_variance_le_of_finite_restrictions ν A hA t
  intro S hS hpos
  let := hS.fintype
  have : IsProbabilityMeasure (subtypeReference ν S) :=
    subtypeReference_probability ν hS.measurableSet hpos
  have h := finite_cylinder_cgf_variance_le hpub (subtypeReference ν S)
    (fun x : S => A x) B hB (fun x => hA x) t
  have he (g : ℕ → ℝ) :
      cgf (fun x : S => cylinderField (A x) g) (subtypeReference ν S) t =
        cgf (fun x => cylinderField (A x) g) (normalizedRestriction ν S) t := by
    unfold cgf mgf
    congr 1
    exact (subtypeReference_preserving ν hS.measurableSet).hasLaw.integral_comp
      (measurable_of_countable (fun x => Real.exp (t * cylinderField (A x) g))).aestronglyMeasurable
  simpa only [he] using h

end InvariantIsing

end

end OAI
