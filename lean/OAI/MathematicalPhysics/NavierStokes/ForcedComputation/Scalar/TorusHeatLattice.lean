import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatInput
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace OAI

/-! Summability, factorization and continuity of the actual periodized Gaussian.
These lemmas address the heat-kernel input, without assuming a heat equation. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff BigOperators

def gaussianLattice (t x : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-((x + (n : ℝ)) ^ 2) / (4 * t))

theorem gaussianLattice_summable {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n : ℤ => Real.exp (-((x + (n : ℝ)) ^ 2) / (4 * t))) := by
  have h := HurwitzKernelBounds.summable_f_int 0 x
    (t := 1 / (4 * Real.pi * t)) (by positivity)
  apply h.congr
  intro n
  simp only [HurwitzKernelBounds.f_int, pow_zero, one_mul]
  congr 1
  field_simp [ht.ne', Real.pi_ne_zero]
  ring

theorem torusHeatKernel_factor {t : ℝ} (ht : 0 < t) (x : Plane) :
    torusHeatKernel t x = (4 * Real.pi * t)⁻¹ *
      (gaussianLattice t (x 0) * gaussianLattice t (x 1)) := by
  unfold torusHeatKernel gaussianLattice
  congr 1
  calc
    (∑' k : Fin 2 → ℤ, Real.exp (-(∑ j : Fin 2, (x j + (k j : ℝ)) ^ 2) / (4 * t))) =
        ∑' k : Fin 2 → ℤ, Real.exp (-((x 0 + (k 0 : ℝ)) ^ 2) / (4 * t)) *
          Real.exp (-((x 1 + (k 1 : ℝ)) ^ 2) / (4 * t)) := by
      apply tsum_congr
      intro k
      rw [← Real.exp_add]
      congr 1
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑' p : ℤ × ℤ, Real.exp (-((x 0 + (p.1 : ℝ)) ^ 2) / (4 * t)) *
          Real.exp (-((x 1 + (p.2 : ℝ)) ^ 2) / (4 * t)) :=
      (finTwoArrowEquiv ℤ).tsum_eq (fun p : ℤ × ℤ =>
        Real.exp (-((x 0 + (p.1 : ℝ)) ^ 2) / (4 * t)) *
          Real.exp (-((x 1 + (p.2 : ℝ)) ^ 2) / (4 * t)))
    _ = _ := (tsum_mul_tsum_of_summable_norm
      (gaussianLattice_summable ht (x 0)).norm
      (gaussianLattice_summable ht (x 1)).norm).symm

theorem gaussianLattice_continuous {t : ℝ} (ht : 0 < t) : Continuous (gaussianLattice t) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let M := |x₀| + 1
  let u := fun n : ℤ => Real.exp (M ^ 2 / (4 * t)) * Real.exp (-((n : ℝ) ^ 2) / (8 * t))
  have hu : Summable u := by
    have hs := (gaussianLattice_summable (t := 2 * t) (by positivity) 0).mul_left
      (Real.exp (M ^ 2 / (4 * t)))
    simpa only [u, zero_add, ← mul_assoc, show (4 : ℝ) * 2 = 8 by norm_num] using hs
  have hc : ContinuousOn (gaussianLattice t) (Metric.ball x₀ 1) := by
    apply continuousOn_tsum (u := u)
    · intro n
      exact (((continuous_id.add continuous_const).pow 2).neg.div_const (4 * t)).rexp.continuousOn
    · exact hu
    · intro n x hx
      have hx' : |x - x₀| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hx
      have hxM : |x| ≤ M := by
        dsimp only [M]
        calc
          |x| ≤ |x - x₀| + |x₀| := by simpa only [sub_add_cancel] using abs_add_le (x - x₀) x₀
          _ ≤ |x₀| + 1 := by linarith
      have hM : 0 ≤ M := by dsimp only [M]; positivity
      have hsq : (n : ℝ) ^ 2 ≤ 2 * (x + (n : ℝ)) ^ 2 + 2 * M ^ 2 := by
        have hxx : x ^ 2 ≤ M ^ 2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hM).mpr hxM
        nlinarith [sq_nonneg ((n : ℝ) + 2 * x)]
      have he : -((x + (n : ℝ)) ^ 2) / (4 * t) ≤
          M ^ 2 / (4 * t) + -((n : ℝ) ^ 2) / (8 * t) := by
        calc
          _ = (-2 * (x + (n : ℝ)) ^ 2) / (8 * t) := by
            field_simp
            ring
          _ ≤ (2 * M ^ 2 - (n : ℝ) ^ 2) / (8 * t) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by
            field_simp
            ring
      dsimp only [u]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      exact Real.exp_le_exp.mpr he
  exact hc.continuousAt (Metric.ball_mem_nhds x₀ zero_lt_one)

theorem torusHeatKernel_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (torusHeatKernel t) := by
  have he : torusHeatKernel t = fun x : Plane => (4 * Real.pi * t)⁻¹ *
      (gaussianLattice t (x 0) * gaussianLattice t (x 1)) := funext (torusHeatKernel_factor ht)
  rw [he]
  exact continuous_const.mul (((gaussianLattice_continuous ht).comp (continuous_apply 0)).mul
    ((gaussianLattice_continuous ht).comp (continuous_apply 1)))

end ForcedComputation.VelocityDetector

end

end OAI
