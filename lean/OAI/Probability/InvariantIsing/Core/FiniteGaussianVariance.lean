import OAI.Probability.InvariantIsing.Haar.PublishedInputs
import OAI.Probability.IsingPerceptron.EnrichedFieldCap
import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi

namespace OAI

/-! Finite Gaussian cutoff partition functions in the Euclidean norm. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal InnerProductSpace

namespace InvariantIsing

/-- The finite-cutoff Gaussian log partition, with arbitrary probability
weights and deterministic base energy. In the application the finite state
space is a positive-mass restriction of the spin/cascade-leaf prior. -/
def finiteGaussianLogPartition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) {d : ℕ}
    (A : X → EuclideanSpace ℝ (Fin d)) (g : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log (∫ x, Real.exp (H x + ⟪A x, g⟫_ℝ) ∂ν)

theorem finiteGaussianLogPartition_lipschitz {X : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) {d : ℕ}
    (A : X → EuclideanSpace ℝ (Fin d)) (L : ℝ≥0) (hA : ∀ x, ‖A x‖ ≤ L) :
    LipschitzWith L (finiteGaussianLogPartition ν H A) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  have hb (x : X) : |(H x + ⟪A x, g⟫_ℝ) - (H x + ⟪A x, h⟫_ℝ)| ≤
      (L : ℝ) * ‖g - h‖ := by
    rw [add_sub_add_left_eq_sub, ← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _))
  have hcomp := logMean_abs_sub_le ν (by norm_num : (0 : ℝ) < 1)
    (show Integrable (fun x => Real.exp (1 * (H x + ⟪A x, g⟫_ℝ))) ν from Integrable.of_finite)
    (show Integrable (fun x => Real.exp (1 * (H x + ⟪A x, h⟫_ℝ))) ν from Integrable.of_finite) hb
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, logMean, one_mul, div_one,
    finiteGaussianLogPartition] using hcomp

/-- The Gaussian Poincaré inequality bounds the finite-cutoff
log partition variance by the coefficient squared norm,
uniformly in the cutoff and base energy. -/
theorem finiteGaussianLogPartition_variance_le (hpub : GaussianLipschitzVarianceInput)
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) {d : ℕ}
    (A : X → EuclideanSpace ℝ (Fin d)) (B : ℝ≥0)
    (hA : ∀ x, ‖A x‖ ^ 2 ≤ B) :
    variance (finiteGaussianLogPartition ν H A)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ B := by
  have hs : ((NNReal.sqrt B : ℝ≥0) : ℝ) ^ 2 = B := by exact_mod_cast NNReal.sq_sqrt B
  have hnorm (x : X) : ‖A x‖ ≤ ((NNReal.sqrt B : ℝ≥0) : ℝ) := by
    have hn := NNReal.coe_nonneg (NNReal.sqrt B)
    nlinarith [hA x, norm_nonneg (A x)]
  exact (hpub d (NNReal.sqrt B) _
    (finiteGaussianLogPartition_lipschitz ν H A (NNReal.sqrt B) hnorm)).trans_eq hs

/-- Finite-state countable-cylinder restriction. A finite family of finitely supported coefficients uses a common
finite prefix, whose Gaussian law is the standard Euclidean Gaussian. -/
theorem finite_cylinder_cgf_variance_le (hpub : GaussianLipschitzVarianceInput)
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (A : X → ℕ →₀ ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) (t : ℝ) :
    variance (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g) ν t)
      gaussianCoordinates ≤ t ^ 2 * B := by
  classical
  obtain ⟨n, hn⟩ := finite_family_support_bound A
  have hs (x : X) : ∀ j ∈ (A x).support, j < n + 1 :=
    fun j hj => hn x j (Finsupp.mem_support_iff.mp hj)
  let V : X → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun x => WithLp.toLp 2 (fun j : Fin (n + 1) => t * A x j)
  let B' : ℝ≥0 := ⟨t ^ 2 * B, mul_nonneg (sq_nonneg t) hB⟩
  have hv (x : X) : ‖V x‖ ^ 2 ≤ B' := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [V, mul_pow, ← Finset.mul_sum,
      ← cylinder_variance_prefix (A x) (hs x)]
    exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg t)
  let F := finiteGaussianLogPartition ν (fun _ => 0) V
  have hF : Measurable F := by
    have hsqrt : (((NNReal.sqrt B' : ℝ≥0) : ℝ)) ^ 2 = B' :=
      by exact_mod_cast NNReal.sq_sqrt B'
    have hnorm (x : X) : ‖V x‖ ≤ ((NNReal.sqrt B' : ℝ≥0) : ℝ) := by
      have hn' := NNReal.coe_nonneg (NNReal.sqrt B')
      nlinarith [hv x, norm_nonneg (V x)]
    exact (finiteGaussianLogPartition_lipschitz ν (fun _ => 0) V (NNReal.sqrt B') hnorm).continuous.measurable
  have hto : MeasurePreserving
      (WithLp.toLp 2 : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin (n + 1)))) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hmp := hto.comp (gaussian_prefix_measurePreserving (n + 1))
  have he : (fun g : ℕ → ℝ => cgf (fun x => cylinderField (A x) g) ν t) =
      F ∘ ((WithLp.toLp 2) ∘ (fun g : ℕ → ℝ => fun j : Fin (n + 1) => g j)) := by
    funext g
    have hi (x : X) : ⟪V x, WithLp.toLp 2 (fun j : Fin (n + 1) => g j)⟫_ℝ =
        t * cylinderField (A x) g := by
      rw [cylinderField_eq_prefix (A x) (hs x)]
      simp only [V, PiLp.inner_apply, RCLike.inner_apply', conj_trivial]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [Function.comp_apply, F, finiteGaussianLogPartition, cgf, mgf, zero_add, hi]
  rw [he]
  change variance (fun g => F ((WithLp.toLp 2 ∘
    (fun g : ℕ → ℝ => fun j : Fin (n + 1) => g j)) g)) gaussianCoordinates ≤ _
  rw [hmp.variance_fun_comp hF.aemeasurable]
  exact finiteGaussianLogPartition_variance_le hpub ν (fun _ => 0) V B' hv

end InvariantIsing

end

end OAI
