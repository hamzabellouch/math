import OAI.Analysis.ProductSpaces.GaussianMoments

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section GaussianScalar
variable {ι : Type uι} [Fintype ι]

lemma integrable_gaussian_quadratic (a : ι → ℝ) (b : ℝ) :
    Integrable (fun x : ι → ℝ => b + ∑ i, a i * x i ^ 2) gaussianVector := by
  apply (integrable_const b).add
  apply integrable_finsetSum
  intro i _
  exact ((gaussian_square_memLp.comp_measurePreserving
    (measurePreserving_eval (fun _ => gaussianReal 0 1) i)).integrable (by norm_num)).const_mul _

lemma gaussian_quadratic_difference (a : ι → ℝ) (b : ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    ((b + ∑ i, a i * z.1 i ^ 2) - (b + ∑ i, a i * z.2 i ^ 2)) / 2 =
      ∑ i, a i * (gaussianVectorRotate z).1 i * (gaussianVectorRotate z).2 i := by
  have he : ∀ i, a i * z.1 i ^ 2 - a i * z.2 i ^ 2 =
      2 * (a i * (gaussianVectorRotate z).1 i * (gaussianVectorRotate z).2 i) := by
    intro i
    rw [← mul_sub, gaussian_polarization (z.1 i, z.2 i)]
    dsimp [gaussianVectorRotate]
    ring
  have hh : (∑ i, a i * z.1 i ^ 2) - (∑ i, a i * z.2 i ^ 2) =
      2 * ∑ i, a i * (gaussianVectorRotate z).1 i * (gaussianVectorRotate z).2 i := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [he, ← Finset.mul_sum]
  linarith

lemma gaussian_quadratic_scalar_excess (a : ι → ℝ) (b K t r : ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (gaussianTail (Real.sqrt 2 * K) / 12) *
      (t * K * Real.sqrt (∑ i, a i ^ 2) - r) ≤
      ∫ x : ι → ℝ, excess t r (b + ∑ i, a i * x i ^ 2) ∂gaussianVector := by
  have hpartial := gaussian_bilinear_excess a K t r hK ht hr
  have hsym := integral_excess_independent_copy (integrable_gaussian_quadratic a b) ht r
  have he : (∫ z : (ι → ℝ) × (ι → ℝ),
      excess t r (((b + ∑ i, a i * z.1 i ^ 2) - (b + ∑ i, a i * z.2 i ^ 2)) / 2)
      ∂gaussianVector.prod gaussianVector) =
      ∫ z : (ι → ℝ) × (ι → ℝ), excess t r (∑ i, a i * z.1 i * z.2 i)
        ∂gaussianVector.prod gaussianVector := by
    simp_rw [gaussian_quadratic_difference a b]
    exact measurePreserving_gaussianVectorRotate.hasLaw.integral_comp (f := fun z : (ι → ℝ) × (ι → ℝ) =>
      excess t r (∑ i, a i * z.1 i * z.2 i)) (by unfold excess; fun_prop)
  rw [he] at hsym
  calc
    _ ≤ (gaussianTail (Real.sqrt 2 * K) / 12) * excess t r (K * Real.sqrt (∑ i, a i ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (gaussianTail_nonneg _) (by norm_num))
      unfold excess
      rw [abs_of_nonneg (mul_nonneg hK (Real.sqrt_nonneg _))]
      simpa only [mul_assoc] using le_max_left (t * (K * Real.sqrt (∑ i, a i ^ 2)) - r) 0
    _ ≤ _ := hpartial.trans hsym

instance gaussianSquareLaw_probability : IsProbabilityMeasure gaussianSquareLaw := by
  unfold gaussianSquareLaw
  infer_instance

lemma gaussian_square_scalar_excess (a : ι → ℝ) (b K t r : ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (gaussianTail (Real.sqrt 2 * K) / 12) *
      (t * K * Real.sqrt (∑ i, a i ^ 2) - r) ≤
      ∫ w : ι → ℝ, excess t r (b + ∑ i, a i * w i)
        ∂Measure.pi (fun _ => gaussianSquareLaw) := by
  have hp : MeasurePreserving (fun x : ι → ℝ => fun i => x i ^ 2) gaussianVector
      (Measure.pi (fun _ => gaussianSquareLaw)) := by
    unfold gaussianVector
    apply measurePreserving_pi (fun _ : ι => gaussianReal 0 1) (fun _ : ι => gaussianSquareLaw)
      (f := fun _ x => x ^ 2)
    intro i
    exact ⟨by fun_prop, rfl⟩
  have he := hp.hasLaw.integral_comp (f := fun w : ι → ℝ => excess t r (b + ∑ i, a i * w i))
    ((by unfold excess; fun_prop : Continuous (fun w : ι → ℝ => excess t r (b + ∑ i, a i * w i))).aestronglyMeasurable)
  exact he ▸ gaussian_quadratic_scalar_excess a b K t r hK ht hr

end GaussianScalar
end IndependentProducts

end

end OAI
