import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PeriodicHeatMass
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatPositiveSmooth
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

/-! Unit mass and the sup-norm estimate for the actual two-dimensional heat kernel. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped BigOperators

theorem torusHeatKernel_integral {t : ℝ} (ht : 0 < t) (x : Plane) :
    (∫ y in Icc (0 : Plane) (fun _ => 1), torusHeatKernel t (x - y)) = 1 := by
  have hc : (∫ y in Icc (0 : Plane) (fun _ => 1),
      (torusHeatKernel t (x - y) : ℂ)) = 1 := by
    simp_rw [torusHeatKernel_complex ht]
    have hp : (fun y : Plane => periodicHeatMoment 0 (t, (x - y) 0) *
        periodicHeatMoment 0 (t, (x - y) 1)) =
        (fun y => ∏ j : Fin 2, periodicHeatMoment 0 (t, x j - y j)) := by
      funext y
      simp [Fin.prod_univ_two]
    rw [hp]
    change (∫ y, ∏ j : Fin 2, periodicHeatMoment 0 (t, x j - y j)
      ∂((Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ))).restrict
        (Icc (0 : Plane) (fun _ => 1)))) = 1
    rw [← pi_univ_Icc, Measure.restrict_pi_pi]
    change (∫ y : Plane, ∏ j : Fin 2, periodicHeatMoment 0 (t, x j - y j)
      ∂Measure.pi (fun _ : Fin 2 => volume.restrict (Icc (0 : ℝ) 1))) = 1
    rw [integral_fintype_prod_eq_prod (fun (j : Fin 2) (y : ℝ) =>
      periodicHeatMoment 0 (t, x j - y))]
    simp [periodicHeatMoment_integral ht]
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

theorem torusHeatEvolution_const (c : ℝ) (t : ℝ) (x : Plane) :
    torusHeatEvolution (fun _ => c) t x = c := by
  by_cases ht : t ≤ 0
  · simp [torusHeatEvolution, ht]
  · rw [torusHeatEvolution, ite_eq_right ht, integral_mul_const,
      torusHeatKernel_integral (lt_of_not_ge ht), one_mul]

theorem torusHeatEvolution_norm_le {g : Plane → ℝ} {B t : ℝ}
    (hB : ∀ x, |g x| ≤ B) (ht : 0 < t) (x : Plane) :
    |torusHeatEvolution g t x| ≤ B := by
  have hK : Continuous (fun y : Plane => torusHeatKernel t (x - y)) :=
    (torusHeatKernel_continuous ht).comp (continuous_const.sub continuous_id)
  have hi : IntegrableOn (fun y : Plane => torusHeatKernel t (x - y) * B)
      (Icc (0 : Plane) (fun _ => 1)) :=
    (hK.mul continuous_const).continuousOn.integrableOn_compact isCompact_Icc
  rw [torusHeatEvolution, ite_eq_right (not_le.mpr ht), ← Real.norm_eq_abs]
  calc
    ‖∫ y in Icc (0 : Plane) (fun _ => 1), torusHeatKernel t (x - y) * g y‖ ≤
        ∫ y in Icc (0 : Plane) (fun _ => 1), torusHeatKernel t (x - y) * B := by
      apply norm_integral_le_of_norm_le hi
      exact ae_of_all _ fun y => by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (torusHeatKernel_nonneg ht _),
          Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB y) (torusHeatKernel_nonneg ht _)
    _ = B := by rw [integral_mul_const, torusHeatKernel_integral ht, one_mul]

end ForcedComputation.VelocityDetector

end

end OAI
