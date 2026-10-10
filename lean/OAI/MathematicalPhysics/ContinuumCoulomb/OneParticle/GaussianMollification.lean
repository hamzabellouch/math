import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GaussianScalar
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ScalarMollification

namespace OAI

/-! Passing the proved Gaussian Poincare inequality to compact C¹ tests. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace ContinuumCoulomb

theorem gaussian_mollification_power_tendsto {freq : ℝ} (hf : 0 < freq)
    (f : ℝ → ℝ) (hs : Continuous f) (hc : HasCompactSupport f) (p : ℕ) :
    Tendsto (fun k => ∫ z : ℝ, verticalMode freq z^2*(scalarMollification f k z)^p)
      atTop (𝓝 (∫ z : ℝ, verticalMode freq z^2*f z^p)) := by
  obtain ⟨C,hC⟩ := hs.bounded_above_of_compact_support hc
  apply tendsto_integral_of_dominated_convergence
    (fun z => verticalMode freq z^2*C^p)
  · intro k
    exact (((verticalMode_smooth freq).continuous.pow 2).mul
      ((scalarMollification_smooth hs k).continuous.pow p)).aestronglyMeasurable
  · exact (verticalMode_square_integrable hf).mul_const _
  · intro k
    apply Filter.Eventually.of_forall
    intro z
    have hb := pow_le_pow_left₀ (norm_nonneg (scalarMollification f k z))
      (scalarMollification_bound hC k z) p
    simpa only [norm_mul,norm_pow,Real.norm_eq_abs,sq_abs] using
      mul_le_mul_of_nonneg_left hb (sq_nonneg (verticalMode freq z))
  · exact Filter.Eventually.of_forall fun z =>
      ((scalarMollification_tendsto hs z).pow p).const_mul _

/-- The normalized Gaussian Poincare inequality on the exact C¹ test domain. -/
theorem gaussian_scalar_poincare {freq : ℝ} (hf : 0 < freq)
    (f : ℝ → ℝ) (hs : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (2*freq)*((∫ z : ℝ, verticalMode freq z^2*f z^2) -
      (∫ z : ℝ, verticalMode freq z^2*f z)^2) ≤
        ∫ z : ℝ, verticalMode freq z^2*(deriv f z)^2 := by
  have h2 := gaussian_mollification_power_tendsto hf f hs.continuous hc 2
  have h1 := gaussian_mollification_power_tendsto hf f hs.continuous hc 1
  simp only [pow_one] at h1
  have hd := gaussian_mollification_power_tendsto hf (deriv f)
    (hs.continuous_deriv (by norm_num)) hc.deriv 2
  apply le_of_tendsto_of_tendsto ((h2.sub (h1.pow 2)).const_mul (2*freq)) hd
  apply Filter.Eventually.of_forall
  intro k
  have h := gaussian_scalar_poincare_smooth hf (scalarMollification f k)
    (scalarMollification_smooth hs.continuous k) (scalarMollification_compact hc k)
  simpa only [scalarMollification_deriv hs hc] using h

end ContinuumCoulomb

end

end OAI
