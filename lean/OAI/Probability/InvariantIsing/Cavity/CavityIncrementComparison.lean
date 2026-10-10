import OAI.Probability.InvariantIsing.Cavity.CavityPerturbationComparison

namespace OAI

/-! The finite cavity increment after absorbing deterministic and
Gaussian covariance errors. The base Gaussian field stays inside the
Gibbs measure in the factor on the right. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_log_tilt_factor {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H W : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (hHW : Integrable (fun x => Real.exp (H x + W x)) ν) :
    Real.log (∫ x, Real.exp (W x) ∂ν.tilted H) =
      Real.log (∫ x, Real.exp (H x + W x) ∂ν) - Real.log (∫ x, Real.exp (H x) ∂ν) := by
  rw [integral_exp_tilted]
  simp only [Pi.add_apply]
  exact Real.log_div (integral_exp_pos hHW).ne' (integral_exp_pos hH).ne' 

lemma cavity_mean_log_tilt_factor {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H W : X → ℝ) {M L : ℝ} (hH : ∀ x, |H x| ≤ M) (hW : ∀ x, |W x| ≤ L)
    (C : X → ℕ →₀ ℝ) {B : ℝ} (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (W x)
      ∂ν.tilted (fun x => H x + cylinderField (C x) g)) ∂gaussianCoordinates) =
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + W x + cylinderField (C x) g) ∂ν)
      ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates := by
  have hHW : ∀ x, |H x + W x| ≤ M + L := fun x =>
    (abs_add_le _ _).trans (add_le_add (hH x) (hW x))
  have hiH := cavity_bounded_base_exp_integrable ν H hH
  have hiHW := cavity_bounded_base_exp_integrable ν (fun x => H x + W x) hHW
  have hpH := (cylinder_log_partition_memLp_two ν H hiH C hC 1).integrable (by norm_num)
  have hpHW := (cylinder_log_partition_memLp_two ν (fun x => H x + W x) hiHW C hC 1).integrable
    (by norm_num)
  simp only [one_mul] at hpH hpHW
  rw [← integral_sub hpHW hpH]
  apply integral_congr_ae
  filter_upwards [cylinder_partition_exp_integrable_ae ν H hiH C hC,
    cylinder_partition_exp_integrable_ae ν (fun x => H x + W x) hiHW C hC] with g hg hgW
  have he (x : X) : H x + W x + cylinderField (C x) g =
      (H x + cylinderField (C x) g) + W x := by ring
  simp_rw [he] at hgW ⊢
  exact cavity_log_tilt_factor ν _ W hg hgW

/-- The actual increment estimate used before passing to cavity limits.
All error bounds concern the conditioned finite-size energies and
covariances; no lower-bound conclusion is assumed. -/
theorem cavity_log_increment_comparison {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H W J V : X → ℝ) (c d : ℝ)
    {M L M₁ D B₀ B₁ : ℝ}
    (hH : ∀ x, |H x| ≤ M) (hW : ∀ x, |W x| ≤ L) (hJ : ∀ x, |J x| ≤ M₁)
    (hV : ∀ x, |V x| ≤ D) (hE : ∀ x, |J x - (H x + W x)| ≤ d * V x)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (V x + V y)) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (W x - (d + 2 * c) * V x)
      ∂ν.tilted (fun x => H x + cylinderField (C x) g)) ∂gaussianCoordinates) ≤
      (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (J x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates := by
  have hHW : ∀ x, |H x + W x| ≤ M + L := fun x =>
    (abs_add_le _ _).trans (add_le_add (hH x) (hW x))
  rw [cavity_mean_log_tilt_factor ν H (fun x => W x - (d + 2 * c) * V x) hH
    (cavity_bounded_sub_mul W V (d + 2 * c) hW hV) C hC]
  have ht := cavity_countable_perturbation_comparison ν (fun x => H x + W x) J V c d
    hHW hJ hV hE C A hC hA hK
  have he (x : X) : H x + (W x - (d + 2 * c) * V x) = H x + W x - (d + 2 * c) * V x := by ring
  simp_rw [he]
  exact sub_le_sub_right ht _

end InvariantIsing

end

end OAI
