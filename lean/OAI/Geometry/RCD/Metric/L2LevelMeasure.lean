import OAI.Geometry.RCD.Sobolev.DirichletPoincare

namespace OAI

/-! # L2 control of the measure of a level set -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- A lower bound on a finite-measure set gives the corresponding L2
level-set estimate, with the actual chosen representative. -/
theorem lp_level_measure_le (u : Lp ℝ 2 μ) {A : Set X} (hAt : μ A ≠ ∞)
    {t : ℝ} (ht : 0 ≤ t) (hbound : ∀ᵐ x ∂μ.restrict A, t ≤ |u x|) :
    t^2 * μ.real A ≤ ‖u‖^2 := by
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa using hAt.lt_top⟩
  have hsq : Integrable (fun x => u x^2) μ := (Lp.memLp u).integrable_sq
  calc
    _ = ∫ _x in A, t^2 ∂μ := by simp [mul_comm]
    _ ≤ ∫ x in A, u x^2 ∂μ := by
      apply integral_mono_ae (integrable_const _) hsq.integrableOn
      filter_upwards [hbound] with x hx
      simpa only [sq_abs] using (sq_le_sq₀ ht (abs_nonneg (u x))).mpr hx
    _ ≤ ∫ x, u x^2 ∂μ :=
      setIntegral_le_integral hsq (Filter.Eventually.of_forall (fun x => sq_nonneg (u x)))
    _ = _ := lp_integral_square_eq_norm_square μ u

/-- Zero boundary values identify the full L2 norm with the integral on
the Dirichlet domain. -/
theorem dirichlet_integral_square_eq_norm_square [MetricSpace X]
    (hQ : QuadraticCheegerEnergy μ) {Ω : Set X} (hΩ : MeasurableSet Ω)
    (w : SobolevSpace.dirichlet μ hQ Ω) :
    (∫ x in Ω, (SobolevSpace.toLp μ hQ w.val x)^2 ∂μ) =
      ‖SobolevSpace.toLp μ hQ w.val‖^2 := by
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero, lp_integral_square_eq_norm_square]
  have hz := SobolevSpace.dirichlet_zero_off μ hQ Ω hΩ w
  filter_upwards [(ae_restrict_iff' hΩ.compl).mp hz] with x hx hnot
  simp [hx hnot]

end RegularPointCoordinates

end

end OAI
