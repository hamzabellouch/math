import OAI.Probability.InvariantIsing.Cavity.CavityUniformComparison
import OAI.Probability.InvariantIsing.Cavity.CavityBoundedSecant

namespace OAI

/-! Bounded test comparison for finite spin/leaf restrictions. A common
test tilt reduces comparison of Gibbs means to the covariance-only
log-partition estimate and a uniform bounded-variable secant bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma finite_cylinder_test_cgf_eq {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H F : X → ℝ) (A : X → ℕ →₀ ℝ) {B : ℝ}
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B) (s : ℝ) :
    (∫ g : ℕ → ℝ, cgf F (ν.tilted (fun x => H x + cylinderField (A x) g)) s
      ∂gaussianCoordinates) =
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + s * F x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates) -
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have he (g : ℕ → ℝ) :
      cgf F (ν.tilted (fun x => H x + cylinderField (A x) g)) s =
      Real.log (∫ x, Real.exp (H x + s * F x + cylinderField (A x) g) ∂ν) -
      Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν) := by
    rw [cgf, mgf, integral_exp_tilted]
    rw [Real.log_div (MeasureTheory.integral_exp_pos Integrable.of_finite).ne'
      (MeasureTheory.integral_exp_pos Integrable.of_finite).ne']
    simp only [Pi.add_apply]
    simp_rw [show ∀ x, (H x + cylinderField (A x) g) + s * F x =
      H x + s * F x + cylinderField (A x) g from fun x => by ring]
  simp_rw [he]
  apply integral_sub
  · simpa only [one_mul] using
      (cylinder_log_partition_memLp_two ν (fun x => H x + s * F x)
        Integrable.of_finite A hA 1).integrable (by norm_num)
  · simpa only [one_mul] using
      (cylinder_log_partition_memLp_two ν H Integrable.of_finite A hA 1).integrable (by norm_num)

theorem cavity_finite_test_comparison {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H J F : X → ℝ) {M₀ M₁ B₀ B₁ K E B s : ℝ}
    (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁) (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (hbase : ∀ x, |H x - J x| ≤ E) (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) (hs : 0 < s) :
    |(∫ g : ℕ → ℝ, ∫ x, F x ∂ν.tilted (fun x => H x + cylinderField (C x) g)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, ∫ x, F x ∂ν.tilted (fun x => J x + cylinderField (A x) g)
        ∂gaussianCoordinates| ≤
      (2 * (2 * K + E)) / s + B ^ 2 * s / 2 := by
  let μ := fun g : ℕ → ℝ => ν.tilted (fun x => H x + cylinderField (C x) g)
  let η := fun g : ℕ → ℝ => ν.tilted (fun x => J x + cylinderField (A x) g)
  have : ∀ g, IsProbabilityMeasure (μ g) := fun _ => isProbabilityMeasure_tilted Integrable.of_finite
  have : ∀ g, IsProbabilityMeasure (η g) := fun _ => isProbabilityMeasure_tilted Integrable.of_finite
  have hμ : Measurable μ := measurable_random_tilted_measure (ν := fun _ : ℕ → ℝ => ν)
    (H := fun z : (ℕ → ℝ) × X => H z.2 + cylinderField (C z.2) z.1) measurable_const
    (((measurable_of_countable H).comp measurable_snd).add (measurable_cylinderFields C))
  have hη : Measurable η := measurable_random_tilted_measure (ν := fun _ : ℕ → ℝ => ν)
    (H := fun z : (ℕ → ℝ) × X => J z.2 + cylinderField (A z.2) z.1) measurable_const
    (((measurable_of_countable J).comp measurable_snd).add (measurable_cylinderFields A))
  apply cavity_bounded_random_test_compare gaussianCoordinates μ η hμ hη (fun _ => F)
    ((measurable_of_countable F).comp measurable_snd) hB (fun _ => hF) hs
  rw [finite_cylinder_test_cgf_eq ν H F C hC s, finite_cylinder_test_cgf_eq ν J F A hA s]
  have hHS : ∀ x, |H x + s * F x| ≤ M₀ + |s| * B := by
    intro x
    exact (abs_add_le _ _).trans (by
      rw [abs_mul]
      exact add_le_add (hH x) (mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)))
  have hJS : ∀ x, |J x + s * F x| ≤ M₁ + |s| * B := by
    intro x
    exact (abs_add_le _ _).trans (by
      rw [abs_mul]
      exact add_le_add (hJ x) (mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)))
  have htilt := countable_cylinder_uniform_comparison ν (fun x => H x + s * F x)
    (fun x => J x + s * F x) hHS hJS C A hC hA hK hcov
    (fun x => by simpa only [add_sub_add_right_eq_sub] using hbase x)
  have hzero := countable_cylinder_uniform_comparison ν H J hH hJ C A hC hA hK hcov hbase
  rw [show ∀ a b c d : ℝ, (a - b) - (c - d) = (a - c) - (b - d) from
    fun a b c d => by ring]
  exact (abs_sub _ _).trans (by linarith [htilt, hzero])

end InvariantIsing

end

end OAI
