import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CappedCoulombKernel

namespace OAI

/-! The exact three-dimensional near-pole mass makes the cap error
quadratic in its rational radius. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem coulomb_kernelBallMass {ε : ℝ} (hε : 0 ≤ ε) :
    NeutralAtom.kernelBallMass ε = 2 * Real.pi * ε ^ 2 := by
  unfold NeutralAtom.kernelBallMass
  rw [← integral_indicator measurableSet_ball]
  have he : (Metric.ball (0 : Position) ε).indicator NeutralAtom.coulombKernel =
      (fun x : Position => (Set.Iio ε).indicator (fun r : ℝ => r⁻¹) ‖x‖) := by
    funext x
    by_cases hx : ‖x‖ < ε
    · simp [NeutralAtom.coulombKernel, Metric.mem_ball, dist_zero_right, hx]
    · simp [Metric.mem_ball, dist_zero_right, hx]
  rw [he, integral_fun_norm_addHaar volume]
  have hi : (∫ r in Set.Ioi (0 : ℝ), r ^ (Module.finrank ℝ Position - 1) •
      (Set.Iio ε).indicator (fun t : ℝ => t⁻¹) r) = ε ^ 2 / 2 := by
    simp only [finrank_euclideanSpace_fin, smul_eq_mul]
    norm_num
    have hm : (fun r : ℝ => r ^ 2 * (Set.Iio ε).indicator (fun t : ℝ => t⁻¹) r) =
        (Set.Iio ε).indicator (fun r : ℝ => r) := by
      funext r
      by_cases hr : r < ε
      · simp only [Set.indicator_apply, Set.mem_Iio, hr, ite_true]
        by_cases hzero : r = 0
        · simp [hzero]
        · field_simp [hzero]
      · simp [hr]
    rw [hm, setIntegral_indicator measurableSet_Iio]
    have hinter : Set.Ioi (0 : ℝ) ∩ Set.Iio ε = Set.Ioo 0 ε := by ext r; rfl
    rw [hinter, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hε, integral_id]
    ring
  rw [hi]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow,
    one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3), smul_eq_mul,
    nsmul_eq_mul]
  norm_num [Position, finrank_euclideanSpace_fin]
  ring

theorem cappedCoulombPotential_error_explicit {ε B : ℝ} (hε : 0 < ε)
    {ρ : Position → ℝ} (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hbound : ∀ x, ρ x ≤ B) (x : Position) :
    |NeutralAtom.potentialOf ρ x - cappedCoulombPotential ε ρ x| ≤
      2 * Real.pi * B * ε ^ 2 := by
  have h := cappedCoulombPotential_error hε hρ hpos hbound x
  rw [coulomb_kernelBallMass hε.le] at h
  convert h using 1
  ring

end ContinuumCoulomb

end

end OAI
