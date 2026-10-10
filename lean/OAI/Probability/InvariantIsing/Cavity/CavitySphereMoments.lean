import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRadialMoments

namespace OAI

/-! Uniform even moments of Haar projections. Gaussian angular averaging
gives a bound with the dimension in the denominator. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace InvariantIsing

theorem cavity_gaussian_angular_moment {n : ℕ}
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (p : ℕ) :
    (∫ z, |⟪v, z⟫| ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ p ∂stdGaussian _) *
        ∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ := by
  let F := fun U : Orthogonal n => fun z : EuclideanSpace ℝ (Fin n) =>
    |⟪v, matrixRotation U z⟫| ^ p
  have hF : Continuous (Function.uncurry F) :=
    (continuous_const.inner (continuous_cavityRotationAction n)).abs.pow p
  have hb (U : Orthogonal n) (z : EuclideanSpace ℝ (Fin n)) :
      |F U z| ≤ ‖v‖ ^ p * ‖z‖ ^ p := by
    dsimp [F]
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      simpa only [(matrixRotation U).norm_map] using abs_real_inner_le_norm v (matrixRotation U z)) p
  have hi : Integrable (Function.uncurry F) (μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
    apply (((cavity_gaussian_norm_pow_integrable n p).const_mul (‖v‖ ^ p)).comp_snd μ).mono'
      hF.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      change |F z.1 z.2| ≤ ‖v‖ ^ p * ‖z.2‖ ^ p
      exact hb z.1 z.2)
  have hrot (U : Orthogonal n) :
      (∫ z, F U z ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        ∫ z, |⟪v, z⟫| ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    calc
      _ = ∫ z, |⟪v, z⟫| ^ p
          ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).map (matrixRotation U) :=
        (integral_map (matrixRotation U).continuous.aemeasurable (by fun_prop)).symm
      _ = _ := by rw [stdGaussian_map]
  calc
    _ = ∫ U, ∫ z, F U z ∂stdGaussian (EuclideanSpace ℝ (Fin n)) ∂μ := by
      simp_rw [hrot]
      simp
    _ = ∫ z, ∫ U, F U z ∂μ ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      integral_integral_swap hi
    _ = ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ p *
        (∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ) ∂stdGaussian _ :=
      integral_congr_ae (ae_of_all _ (fun z => cavity_sphere_radial_average μ v u z hu p))
    _ = _ := integral_mul_const _ _

theorem cavity_sphere_even_moment_bound {n : ℕ} (hn : 0 < n)
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (v u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (k : ℕ) :
    (∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ) ≤
      cavityGaussianAbsMoment (2 * k) * ‖v‖ ^ (2 * k) / (n : ℝ) ^ k := by
  have hp : (0 : ℝ) < (n : ℝ) ^ k := pow_pos (Nat.cast_pos.mpr hn) k
  apply (le_div_iff₀ hp).mpr
  have hnon : 0 ≤ ∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ :=
    integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) _)
  calc
    _ = (n : ℝ) ^ k * ∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ := mul_comm _ _
    _ ≤ (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ (2 * k) ∂stdGaussian _) *
        ∫ U, |⟪v, matrixRotation U u⟫| ^ (2 * k) ∂μ :=
      mul_le_mul_of_nonneg_right (cavity_gaussian_radial_moment_lower n k) hnon
    _ = cavityGaussianAbsMoment (2 * k) * ‖v‖ ^ (2 * k) := by
      rw [← cavity_gaussian_angular_moment μ v u hu, cavity_gaussian_inner_abs_moment, mul_comm]

end InvariantIsing

end

end OAI
