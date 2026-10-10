import OAI.MeasureTheory.Falconer.Shells.SmoothShellPartition
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def sourceShellMultiplier (τ : Measure ℝ) (n : ℕ) (r : ℝ) : ℂ :=
  (sourceShellBand n r : ℂ) * charFun τ r

theorem sourceShellMultiplier_continuous (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) :
    Continuous (sourceShellMultiplier τ n) :=
  (Complex.continuous_ofReal.comp (sourceShellBand_smooth n).continuous).mul continuous_charFun

theorem sourceShellMultiplier_zero (τ : Measure ℝ) (n : ℕ) (r : ℝ)
    (hr : r ∉ dyadicShell (n+1)) : sourceShellMultiplier τ n r = 0 := by
  have he : sourceShellBand n r = 0 := by
    by_contra hn
    exact hr (sourceShellBand_support n hn)
  simp only [sourceShellMultiplier, he, Complex.ofReal_zero, zero_mul]

theorem sourceShellMultiplier_compact (τ : Measure ℝ) (n : ℕ) :
    HasCompactSupport (sourceShellMultiplier τ n) :=
  HasCompactSupport.intro (dyadicShell_compact (n+1)) (sourceShellMultiplier_zero τ n)

theorem sourceShellMultiplier_memLp (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) (p : ℝ≥0∞) :
    MemLp (sourceShellMultiplier τ n) p volume :=
  (sourceShellMultiplier_continuous τ n).memLp_of_hasCompactSupport
    (sourceShellMultiplier_compact τ n)

theorem sourceShellMultiplier_energy_le (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) :
    (∫ r, ‖sourceShellMultiplier τ n r‖^2) ≤ shellEnergy τ (n+1) := by
  have he : (∫ r in dyadicShell (n+1), ‖sourceShellMultiplier τ n r‖^2) =
      ∫ r, ‖sourceShellMultiplier τ n r‖^2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by
      rw [sourceShellMultiplier_zero τ n r hr, norm_zero, zero_pow (by norm_num)])
  rw [← he]
  apply setIntegral_mono_on
    (((sourceShellMultiplier_continuous τ n).norm.pow 2).continuousOn.integrableOn_compact
      (dyadicShell_compact (n+1))) (shell_energy_integrable τ (n+1))
    (dyadicShell_compact (n+1)).measurableSet
  intro r _
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [sourceShellMultiplier, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (sourceShellBand_abs_le n r) (norm_nonneg _)).trans_eq
    (one_mul _)

end PlanarFalconer

end OAI
