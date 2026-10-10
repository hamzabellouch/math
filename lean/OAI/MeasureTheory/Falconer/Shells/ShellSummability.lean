import OAI.MeasureTheory.Falconer.Graphs.SourceSpatialEnergy
import OAI.MeasureTheory.Falconer.Estimates.SignedConvolution
import Mathlib.MeasureTheory.Function.LpSpace.Complete

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal Topology

 theorem summable_dyadic_decay {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (2:ℝ)^(-a*(n:ℝ))) := by
  have hq : (2:ℝ)^(-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  convert summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) (-a)) hq using 1
  funext n
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

noncomputable def shellL2Term (τN : ℕ → FiniteMeasure ℝ) (n : ℕ) : Lp (α := ℝ) ℂ 2 volume :=
  (shellKernelMeasureConvolution_L2 (τN (n+1)) n).1.toLp
    (kernelMeasureConvolution (sourceShellKernel n) (τN (n+1)))

noncomputable def shellL1Error (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ)
    (n : ℕ) : Lp (α := ℝ) ℂ 1 volume :=
  (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_sub_L1 τ (τN (n+1)) n).1).toLp
    (fun x => kernelMeasureConvolution (sourceShellKernel n) τ x-
      kernelMeasureConvolution (sourceShellKernel n) (τN (n+1)) x)

 theorem shellL2Term_norm_sq_le (τN : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    ‖shellL2Term τN n‖^2 ≤ (2*Real.pi)⁻¹ * shellEnergy (τN (n+1)) (n+1) := by
  rw [shellL2Term, ← integral_sq_norm_toLp]
  exact (shellKernelMeasureConvolution_L2 (τN (n+1)) n).2

 theorem shellL2Term_norm_summable (τN : ℕ → FiniteMeasure ℝ)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 0 < C) (N₀ : ℕ)
    (hb : ∀ N ≥ N₀, shellEnergy (τN N) N ≤ C*(2:ℝ)^(-γ*(N:ℝ))) :
    Summable (fun n => ‖shellL2Term τN n‖) := by
  have hs := (summable_dyadic_decay (half_pos hγ)).mul_left (Real.sqrt ((2*Real.pi)⁻¹*C))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (2*Real.pi)⁻¹ * shellEnergy (τN (n+1)) (n+1) := shellL2Term_norm_sq_le τN n
    _ ≤ (2*Real.pi)⁻¹ * (C*(2:ℝ)^(-γ*((n+1:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left (hb _ (by omega)) (by positivity)
    _ ≤ (2*Real.pi)⁻¹ * (C*(2:ℝ)^(-γ*(n:ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith
    _ = (Real.sqrt ((2*Real.pi)⁻¹*C) * (2:ℝ)^(-(γ/2)*(n:ℝ)))^2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (by norm_num)]
      rw [← mul_assoc]
      congr 2
      push_cast
      ring

end PlanarFalconer

end OAI
