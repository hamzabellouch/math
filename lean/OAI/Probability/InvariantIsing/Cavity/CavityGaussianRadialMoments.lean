import OAI.Probability.InvariantIsing.Cavity.CavitySphereAverage

namespace OAI

/-! Dimension-explicit Gaussian radial moments used to bound moments of
uniform spherical projections. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace InvariantIsing

def cavityGaussianAbsMoment (p : ℕ) : ℝ :=
  ∫ z : ℝ, |z| ^ p ∂gaussianReal 0 1

lemma cavityGaussianAbsMoment_nonneg (p : ℕ) : 0 ≤ cavityGaussianAbsMoment p :=
  integral_nonneg (fun z => pow_nonneg (abs_nonneg z) p)

lemma cavityGaussianAbsMoment_two : cavityGaussianAbsMoment 2 = 1 := by
  have h := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa only [cavityGaussianAbsMoment, id_eq, integral_id_gaussianReal,
    sub_zero, sq_abs, NNReal.coe_one] using h

lemma cavity_gaussian_norm_pow_integrable (n p : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ p) (stdGaussian _) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin n))) p (by simp)).integrable_norm_pow'

lemma cavity_gaussian_inner_abs_moment {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (p : ℕ) :
    (∫ z, |⟪v, z⟫| ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ‖v‖ ^ p * cavityGaussianAbsMoment p := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) := innerSL ℝ v
  have hm : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L =
      (gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, gaussianReal_map_const_mul]
    simp only [L, innerSL_apply_norm, mul_zero, mul_one]
    congr 1
    exact NNReal.eq (by simp)
  calc
    _ = ∫ z : ℝ, |z| ^ p ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).map L :=
      (integral_map L.continuous.aemeasurable (by fun_prop)).symm
    _ = ∫ z : ℝ, |z| ^ p ∂(gaussianReal 0 1).map (fun x : ℝ => ‖v‖ * x) := by rw [hm]
    _ = ‖v‖ ^ p * cavityGaussianAbsMoment p := by
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [abs_mul, abs_norm, mul_pow, integral_const_mul, cavityGaussianAbsMoment]

lemma cavity_gaussian_norm_sq_integral (n : ℕ) :
    (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 ∂stdGaussian _) = n := by
  have hcoord (i : Fin n) :
      (∫ z : EuclideanSpace ℝ (Fin n), z i ^ 2 ∂stdGaussian _) = 1 := by
    have h := cavity_gaussian_inner_abs_moment (EuclideanSpace.basisFun (Fin n) ℝ i) 2
    simpa only [EuclideanSpace.basisFun_inner, sq_abs,
      OrthonormalBasis.norm_eq_one, one_pow, one_mul, cavityGaussianAbsMoment_two] using h
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  · intro i _
    simpa only [innerSL_apply_apply, EuclideanSpace.basisFun_inner, Real.norm_eq_abs, sq_abs] using
      (IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)) 2 (by simp)).integrable_norm_pow'

lemma cavity_gaussian_radial_moment_lower (n k : ℕ) :
    (n : ℝ) ^ k ≤ ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ (2 * k) ∂stdGaussian _ := by
  have hi : Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2)
      (stdGaussian _) := cavity_gaussian_norm_pow_integrable n 2
  have hik : Integrable (fun z : EuclideanSpace ℝ (Fin n) => (‖z‖ ^ 2) ^ k)
      (stdGaussian _) := by
    simpa only [← pow_mul] using cavity_gaussian_norm_pow_integrable n (2 * k)
  have h := (convexOn_pow k (𝕜 := ℝ)).map_integral_le (by fun_prop)
    isClosed_Ici (ae_of_all _ (fun z => sq_nonneg ‖z‖)) hi hik
  simpa only [cavity_gaussian_norm_sq_integral, ← pow_mul] using h

end InvariantIsing

end

end OAI
