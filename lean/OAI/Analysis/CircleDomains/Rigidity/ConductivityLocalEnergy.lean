import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWitness

namespace OAI

/-! The exact finite-disk energy balance for the constructed conductivity
system. The Jacobian and the vertical boundary flux remain explicit;
neither is replaced by an assumed energy estimate. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace PlaneLocalWeakComplex

 theorem conductivity_local_energy_balance {f : EuclideanPlane → ℂ}
    (D : PlaneLocalWeakComplex f) (R : ℝ) {F : Set EuclideanPlane}
    (hF : MeasurableSet F) (n : ℕ)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) :
    (∫ x in Metric.ball 0 R,
      (D.imagGradient x 0) ^ 2 + (D.imagGradient x 1 - 1) ^ 2) +
      ((n : ℝ) - 1) * (∫ x in Metric.ball 0 R ∩ F,
        (D.imagGradient x 0) ^ 2 + (D.imagGradient x 1) ^ 2) =
    (∫ x in Metric.ball 0 R,
      D.realGradient x 0 * D.imagGradient x 1 - D.realGradient x 1 * D.imagGradient x 0) -
      2 * (∫ x in Metric.ball 0 R, D.imagGradient x 1) +
      (volume (Metric.ball (0 : EuclideanPlane) R)).toReal := by
  classical
  let B : Set EuclideanPlane := Metric.ball 0 R
  let μ := volume.restrict B
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let E : EuclideanPlane → ℝ := fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1)^2
  let H : EuclideanPlane → ℝ := fun x => (D.imagGradient x 0)^2 + (D.imagGradient x 1-1)^2
  let J : EuclideanPlane → ℝ := fun x =>
    D.realGradient x 0 * D.imagGradient x 1 - D.realGradient x 1 * D.imagGradient x 0
  have hE : Integrable E μ := (D.imag_memLp R 0).integrable_sq.add
    (D.imag_memLp R 1).integrable_sq
  have hH : Integrable H μ := (D.imag_memLp R 0).integrable_sq.add
    ((D.imag_memLp R 1).sub (memLp_const 1)).integrable_sq
  have hI : Integrable (F.indicator E) μ := hE.indicator hF
  have hv : Integrable (fun x => D.imagGradient x 1) μ :=
    (D.imag_memLp R 1).integrable (by norm_num)
  have he : J =ᵐ[μ] fun x => H x + ((n : ℝ)-1) * F.indicator E x +
      2 * D.imagGradient x 1 - 1 := by
    filter_upwards [ae_restrict_of_ae hsys] with x hx
    have hh := conductivity_energy_identity hx.1 hx.2
    have ht : (conductivityValue F n x - 1) * E x = ((n : ℝ)-1) * F.indicator E x := by
      by_cases hxF : x ∈ F <;> simp [conductivityValue, hxF]
    change H x + (conductivityValue F n x - 1) * E x = J x - 2 * D.imagGradient x 1 + 1 at hh
    rw [ht] at hh
    linarith
  have hJI : (∫ x, J x ∂μ) = (∫ x, H x ∂μ) + ((n : ℝ)-1) *
      (∫ x, F.indicator E x ∂μ) + 2 * (∫ x, D.imagGradient x 1 ∂μ) -
      (volume B).toReal := by
    have hsum₁ : Integrable (fun x => H x + ((n : ℝ)-1) * F.indicator E x) μ :=
      hH.add (hI.const_mul ((n : ℝ)-1))
    have hsum₂ : Integrable (fun x => H x + ((n : ℝ)-1) * F.indicator E x +
        2 * D.imagGradient x 1) μ := hsum₁.add (hv.const_mul 2)
    rw [integral_congr_ae he, integral_sub hsum₂ (integrable_const 1),
      integral_add hsum₁ (hv.const_mul 2),
      integral_add hH (hI.const_mul ((n : ℝ)-1)), integral_const_mul, integral_const_mul]
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real, μ, Measure.restrict_apply_univ]
  have hIeq : (∫ x, F.indicator E x ∂μ) = ∫ x in B ∩ F, E x := by
    rw [integral_indicator hF, Measure.restrict_restrict hF]
    rw [inter_comm]
  change (∫ x, H x ∂μ) + ((n : ℝ)-1) * (∫ x in B ∩ F, E x) =
    (∫ x, J x ∂μ) - 2 * (∫ x, D.imagGradient x 1 ∂μ) + (volume B).toReal
  rw [hJI, hIeq]
  ring

end PlaneLocalWeakComplex
end CircleDomainRigidity

end

end OAI
