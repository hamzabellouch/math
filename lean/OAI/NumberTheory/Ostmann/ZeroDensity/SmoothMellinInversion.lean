import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothMellinBounds

namespace OAI

/-! # Mellin inversion for the concrete prime-mean test -/

namespace Ostmann

open MeasureTheory Set Filter
open scoped Topology

noncomputable def complexPrimeMeanTest (t : ℝ) : ℂ := primeMeanTest t

theorem complexPrimeMeanTest_continuous : Continuous complexPrimeMeanTest :=
  Complex.continuous_ofReal.comp (primeMeanTest_contDiff (n := 0)).continuous

theorem primeMeanMellin_eq_mellin : primeMeanMellin = mellin complexPrimeMeanTest := by
  funext s
  unfold primeMeanMellin mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (primeMeanTest t : ℂ) * Complex.exp ((s - 1) * (Real.log t : ℂ)) =
    (t : ℂ) ^ (s - 1) * complexPrimeMeanTest t
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt ht),
    ← Complex.ofReal_log (le_of_lt ht)]
  simp only [complexPrimeMeanTest, mul_comm]

theorem complexPrimeMeanTest_bigO_atTop (a : ℝ) :
    complexPrimeMeanTest =O[atTop] (fun t : ℝ => t ^ (-a)) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hz := primeMeanTest_zero_outside t (by intro h; linarith [h.2])
  simp [complexPrimeMeanTest, hz]

theorem complexPrimeMeanTest_bigO_zero (b : ℝ) :
    complexPrimeMeanTest =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  have hz := primeMeanTest_zero_outside t (by intro h; linarith [h.1])
  simp [complexPrimeMeanTest, hz]

theorem primeMeanMellin_differentiable : Differentiable ℂ primeMeanMellin := by
  rw [primeMeanMellin_eq_mellin]
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow
    (complexPrimeMeanTest_continuous.locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (complexPrimeMeanTest_bigO_atTop (s.re + 1)) (by linarith)
    (complexPrimeMeanTest_bigO_zero (s.re - 1)) (by linarith)

theorem complexPrimeMeanTest_mellinConvergent (s : ℂ) :
    MellinConvergent complexPrimeMeanTest s :=
  mellinConvergent_of_isBigO_rpow
    (complexPrimeMeanTest_continuous.locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (complexPrimeMeanTest_bigO_atTop (s.re + 1)) (by linarith)
    (complexPrimeMeanTest_bigO_zero (s.re - 1)) (by linarith)

theorem primeMeanMellin_verticalIntegrable : Complex.VerticalIntegrable primeMeanMellin 2 := by
  obtain ⟨C, hC, hbound⟩ := primeMeanMellin_decay
  have hmajor : Integrable (fun y : ℝ => C * (1 + ‖y‖) ^ (-(8 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 8)).const_mul C
  apply hmajor.mono'
    (primeMeanMellin_differentiable.continuous.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards with y
  have hh := hbound ((2 : ℂ) + (y : ℂ) * Complex.I) (by norm_num) (by norm_num)
  simpa [Real.norm_eq_abs, Real.rpow_def_of_pos (show 0 < 1 + |y| by positivity),
    mul_comm] using hh

/-- Inversion on Re(s)=2, used before shifting the explicit-formula contour. -/
theorem primeMeanTest_mellin_inversion (x : ℝ) (hx : 0 < x) :
    mellinInv 2 primeMeanMellin x = (primeMeanTest x : ℂ) := by
  rw [primeMeanMellin_eq_mellin]
  exact mellinInv_mellin_eq 2 complexPrimeMeanTest hx
    (complexPrimeMeanTest_mellinConvergent 2)
    (by rw [← primeMeanMellin_eq_mellin]; exact primeMeanMellin_verticalIntegrable)
    complexPrimeMeanTest_continuous.continuousAt

end Ostmann

end OAI
