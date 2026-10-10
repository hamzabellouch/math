import OAI.Probability.InvariantIsing.Cavity.CavityPerturbationComparison

namespace OAI

/-! Uniform covariance comparison on a fixed cavity cutoff. The bound
also holds after adding any common bounded replica-test energy. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cylinder_log_mean_const_add {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B) (c : ℝ) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (c + H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates) =
    c + ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have he : (fun g : ℕ → ℝ => Real.log
      (∫ x, Real.exp (c + H x + cylinderField (A x) g) ∂ν)) =ᵐ[gaussianCoordinates]
      (fun g => c + Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)) := by
    filter_upwards [cylinder_partition_exp_integrable_ae ν H hH A hA] with g hg
    simpa only [logMean, one_mul, div_one, add_assoc] using
      logMean_const_add ν (by norm_num : (1 : ℝ) ≠ 0)
        (by simpa only [one_mul] using hg) c
  rw [integral_congr_ae he]
  have hi := (cylinder_log_partition_memLp_two ν H hH A hA 1).integrable (by norm_num)
  simp only [one_mul] at hi
  rw [integral_add (integrable_const _) hi]
  simp only [integral_const, probReal_univ, one_smul]

lemma countable_cylinder_covariance_mean_le {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) {M : ℝ}
    (hH : ∀ x, |H x| ≤ M) (C A : X → ℕ →₀ ℝ) {B₀ B₁ K : ℝ}
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁) (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
      ∂gaussianCoordinates) ≤
    2 * K + ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have hb : ∀ x, |2 * K + H x| ≤ 2 * K + M := by
    intro x
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg (mul_nonneg (by norm_num) hK)]; linarith [hH x])
  have h := countable_cylinder_covariance_penalty_comparison ν (fun x => 2 * K + H x)
    (fun _ => 1) K hb (show ∀ _x : X, |(1 : ℝ)| ≤ 1 from fun _ => by norm_num) C A hC hA
    (fun x y => (hcov x y).trans (by nlinarith))
  have he (x : X) : 2 * K + H x - 2 * K * (1 : ℝ) = H x := by ring
  simp_rw [he] at h
  rwa [cylinder_log_mean_const_add ν H (cavity_bounded_base_exp_integrable ν H hH) A hA] at h

theorem countable_cylinder_uniform_comparison {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H J : X → ℝ)
    {M₀ M₁ B₀ B₁ K E : ℝ} (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁) (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (hbase : ∀ x, |H x - J x| ≤ E) :
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (J x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates| ≤ 2 * K + E := by
  have h₁ := countable_cylinder_covariance_mean_le ν H hH C A hC hA hK hcov
  have h₂ := countable_cylinder_covariance_mean_le ν H hH A C hA hC hK
    (fun x y => by simpa only [abs_sub_comm] using hcov x y)
  have hG : |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates| ≤ 2 * K := abs_le.mpr ⟨by linarith, by linarith⟩
  have hD := countable_cylinder_log_mean_base_compare ν H J
    (cavity_bounded_base_exp_integrable ν H hH) (cavity_bounded_base_exp_integrable ν J hJ)
    A hA hbase
  exact (abs_sub_le _ _ _).trans (add_le_add hG hD)

end InvariantIsing

end

end OAI
