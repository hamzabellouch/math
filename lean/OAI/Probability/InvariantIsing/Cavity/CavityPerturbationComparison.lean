import OAI.Probability.InvariantIsing.Cavity.CavityCountablePenalty

namespace OAI

/-! Deterministic and Gaussian perturbation errors are absorbed by the
same nonuniform cavity penalty on the countable spin/leaf prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cylinder_log_mean_mono {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H J : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (hJ : Integrable (fun x => Real.exp (J x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B)
    (hle : ∀ x, H x ≤ J x) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates) ≤
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (J x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have hiH := (cylinder_log_partition_memLp_two ν H hH A hA 1).integrable (by norm_num)
  have hiJ := (cylinder_log_partition_memLp_two ν J hJ A hA 1).integrable (by norm_num)
  simp only [one_mul] at hiH hiJ
  apply integral_mono_ae hiH hiJ
  filter_upwards [cylinder_partition_exp_integrable_ae ν H hH A hA,
    cylinder_partition_exp_integrable_ae ν J hJ A hA] with g hgH hgJ
  have h := logMean_mono ν (b := 1)
    (F := fun x => H x + cylinderField (A x) g)
    (G := fun x => J x + cylinderField (A x) g) (by norm_num)
    (by simpa only [one_mul] using hgH) (by simpa only [one_mul] using hgJ)
    (fun x => add_le_add (hle x) le_rfl)
  simpa only [logMean, div_one, one_mul] using h

lemma cavity_bounded_sub_mul {X : Type*} (H V : X → ℝ) (k : ℝ)
    {M D : ℝ} (hH : ∀ x, |H x| ≤ M) (hV : ∀ x, |V x| ≤ D) :
    ∀ x, |H x - k * V x| ≤ M + |k| * D := by
  intro x
  exact (abs_sub _ _).trans (by
    rw [abs_mul]
    exact add_le_add (hH x) (mul_le_mul_of_nonneg_left (hV x) (abs_nonneg _)))

theorem cavity_countable_perturbation_comparison {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H J V : X → ℝ) (c d : ℝ)
    {M₀ M₁ D : ℝ} (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (hV : ∀ x, |V x| ≤ D) (hE : ∀ x, |J x - H x| ≤ d * V x)
    (C A : X → ℕ →₀ ℝ) {B₀ B₁ : ℝ}
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (V x + V y)) :
    (∫ g : ℕ → ℝ, Real.log
      (∫ x, Real.exp (H x - (d + 2 * c) * V x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates) ≤
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (J x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have hm := cylinder_log_mean_mono ν (fun x => H x - (d + 2 * c) * V x)
    (fun x => J x - 2 * c * V x)
    (cavity_bounded_base_exp_integrable ν _ (cavity_bounded_sub_mul H V _ hH hV))
    (cavity_bounded_base_exp_integrable ν _ (cavity_bounded_sub_mul J V _ hJ hV))
    C hC (fun x => by linarith [(abs_le.mp (hE x)).1])
  exact hm.trans (countable_cylinder_covariance_penalty_comparison ν J V c hJ hV C A hC hA hK)

end InvariantIsing

end

end OAI
