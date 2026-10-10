import OAI.Probability.InvariantIsing.Cavity.CavityBaseExhaustion

namespace OAI

/-! Uniform finite-volume bounds used to average the actual cavity
increment.  The Gaussian base remains inside the Gibbs probability. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_bounded_base_log_mean_bound {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) {M : ℝ} (hH : ∀ x, |H x| ≤ M)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B) :
    |∫ z, Real.log (∫ x, Real.exp (H x+cylinderField (A x) z) ∂ν)
      ∂gaussianCoordinates| ≤ 1+2*M^2+8*Real.exp (2*B) := by
  let L := fun z : ℕ → ℝ => Real.log (∫ x, Real.exp (H x+cylinderField (A x) z) ∂ν)
  have hm : Measurable L :=
    (((measurable_of_countable H).comp measurable_snd).add
      (measurable_cylinderFields A)).exp.stronglyMeasurable.integral_prod_right'.measurable.log
  have h2 : MemLp L 2 gaussianCoordinates := by
    simpa only [L, one_mul] using cylinder_log_partition_memLp_two ν H
      (cavity_bounded_base_exp_integrable ν H hH) A hA 1
  have hi := h2.integrable (by norm_num)
  have his : Integrable (fun z => L z^2) gaussianCoordinates :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp h2
  have hb := cavity_bounded_base_log_second ν H hH A hA
  calc
    |∫ z, L z ∂gaussianCoordinates| ≤ ∫ z, |L z| ∂gaussianCoordinates :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, (1+L z^2) ∂gaussianCoordinates := by
      apply integral_mono hi.abs ((integrable_const 1).add his)
      intro z
      change |L z| ≤ 1+L z^2
      nlinarith [sq_nonneg (|L z|-1), sq_abs (L z)]
    _ = 1+∫ z, L z^2 ∂gaussianCoordinates := by
      rw [integral_add (integrable_const 1) his]
      simp
    _ ≤ _ := by linarith

lemma cavity_bounded_log_weight_mean_bound {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) {M : ℝ} (hH : ∀ x, |H x| ≤ M)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B)
    (W : X → ℝ) {C : ℝ} (hW : ∀ x, |W x| ≤ C) :
    |∫ z, Real.log (∫ x, Real.exp (W x)
      ∂ν.tilted (fun x => H x+cylinderField (A x) z)) ∂gaussianCoordinates| ≤ C := by
  have he := cylinder_partition_exp_integrable_ae ν H
    (cavity_bounded_base_exp_integrable ν H hH) A hA
  have hb : ∀ᵐ z ∂gaussianCoordinates, ‖Real.log (∫ x, Real.exp (W x)
      ∂ν.tilted (fun x => H x+cylinderField (A x) z))‖ ≤ C := by
    filter_upwards [he] with z hz
    let : IsProbabilityMeasure (ν.tilted (fun x => H x+cylinderField (A x) z)) :=
      isProbabilityMeasure_tilted hz
    simpa only [Real.norm_eq_abs, logMean, one_mul, div_one] using
      logMean_bounds (ν.tilted (fun x => H x+cylinderField (A x) z))
        (measurable_of_countable W) (by norm_num : (0 : ℝ)<1) hW
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

end InvariantIsing

end

end OAI
