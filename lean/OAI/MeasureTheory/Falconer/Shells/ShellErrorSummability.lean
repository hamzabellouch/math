import OAI.MeasureTheory.Falconer.Shells.ShellSummability

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal Topology

 theorem shellL1Error_norm_le (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    ‖shellL1Error τ τN n‖ ≤ (variationDistance τ (τN (n+1))).toReal *
      ∫ x, ‖sourceShellKernel 0 x‖ := by
  have hi := (shellKernelMeasureConvolution_sub_L1 τ (τN (n+1)) n).1
  rw [shellL1Error, Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  exact (shellKernelMeasureConvolution_sub_L1 τ (τN (n+1)) n).2

 theorem shellL1Error_norm_summable (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ)
    {η C : ℝ} (hη : 0 < η) (hC : 0 < C) (N₀ : ℕ)
    (hb : ∀ N ≥ N₀, variationDistance τ (τN N) ≤ ENNReal.ofReal (C*(2:ℝ)^(-η*(N:ℝ)))) :
    Summable (fun n => ‖shellL1Error τ τN n‖) := by
  let K := ∫ x, ‖sourceShellKernel 0 x‖
  have hK : 0 ≤ K := integral_nonneg (fun x => norm_nonneg _)
  have hs := (summable_dyadic_decay hη).mul_left (C*K)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ (variationDistance τ (τN (n+1))).toReal * K := shellL1Error_norm_le τ τN n
    _ ≤ (C*(2:ℝ)^(-η*((n+1:ℕ):ℝ))) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb (n+1) (by omega))
      rw [ENNReal.toReal_ofReal (show 0 ≤ C*(2:ℝ)^(-η*((n+1:ℕ):ℝ)) by positivity)] at h
      exact h
    _ ≤ (C*(2:ℝ)^(-η*(n:ℝ))) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith
    _ = _ := by ring

 theorem shell_approximations_summable (τ : FiniteMeasure ℝ) (hτ : HasShellApproximations τ) :
    ∃ τN : ℕ → FiniteMeasure ℝ,
      Summable (fun n => ‖shellL2Term τN n‖) ∧
      Summable (fun n => ‖shellL1Error τ τN n‖) ∧
      Summable (shellL2Term τN) ∧ Summable (shellL1Error τ τN) := by
  obtain ⟨τN,η,γ,Ctv,Cshell,hη,hγ,hCtv,hCshell,N₀,hb⟩ := hτ
  have h2 := shellL2Term_norm_summable τN hγ hCshell N₀ (fun N hN => (hb N hN).2)
  have h1 := shellL1Error_norm_summable τ τN hη hCtv N₀ (fun N hN => (hb N hN).1)
  exact ⟨τN,h2,h1,h2.of_norm,h1.of_norm⟩

end PlanarFalconer

end OAI
