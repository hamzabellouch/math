import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWeightedBilinearBound

namespace OAI

/-! # A concrete smooth logarithmic cutoff for the quadratic Poisson kernel -/

namespace Ostmann

open scoped SchwartzMap

noncomputable def quadraticLogBump : ContDiffBump (0 : ℝ) :=
  ⟨2, 3, by norm_num, by norm_num⟩

noncomputable def quadraticLogWindow (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) : 𝓢(ℝ, ℂ) :=
  (show HasCompactSupport (fun u : ℝ =>
      (quadraticLogBump u : ℂ) * ρ (X * Real.exp (-u))) from
    (quadraticLogBump.hasCompactSupport.comp_left
      (show Complex.ofReal 0 = 0 by simp)).mul_right).toSchwartzMap (by
        apply ContDiff.mul
        · exact Complex.ofRealCLM.contDiff.comp quadraticLogBump.contDiff
        · exact (ρ.smooth ⊤).comp (by fun_prop))

 theorem quadraticLogWindow_apply (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) :
    quadraticLogWindow ρ X u = (quadraticLogBump u : ℂ) * ρ (X * Real.exp (-u)) := rfl

 theorem quadraticLogWindow_eq (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) (hu : |u| ≤ 2) :
    quadraticLogWindow ρ X u = ρ (X * Real.exp (-u)) := by
  have hb : quadraticLogBump u = 1 := quadraticLogBump.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, quadraticLogBump] using hu)
  rw [quadraticLogWindow_apply, hb, Complex.ofReal_one, one_mul]

noncomputable def quadraticLogKernel (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) : 𝓢(ℝ, ℂ) :=
  (quadraticLogWindow ρ (X / (N : ℝ) ^ 2)).compSubConstCLM ℂ (2 * Real.log N)

 theorem quadratic_log_kernel_identity (ρ : 𝓢(ℝ, ℂ)) (X : ℝ)
    {N s t : ℕ} (hN : 0 < N) (hs : N ≤ s) (hs₂ : s ≤ 2 * N)
    (ht : N ≤ t) (ht₂ : t ≤ 2 * N) :
    quadraticLogKernel ρ X N (Real.log s + Real.log t) = ρ (X / ((s : ℝ) * t)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (0 : ℝ) < s := hNR.trans_le (by exact_mod_cast hs)
  have htR : (0 : ℝ) < t := hNR.trans_le (by exact_mod_cast ht)
  have hslo : Real.log N ≤ Real.log s := Real.log_le_log hNR (by exact_mod_cast hs)
  have htlo : Real.log N ≤ Real.log t := Real.log_le_log hNR (by exact_mod_cast ht)
  have hsu : Real.log s ≤ Real.log 2 + Real.log N := by
    have hh := Real.log_le_log hsR (show (s : ℝ) ≤ 2 * N by exact_mod_cast hs₂)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNR.ne'] at hh
  have htu : Real.log t ≤ Real.log 2 + Real.log N := by
    have hh := Real.log_le_log htR (show (t : ℝ) ≤ 2 * N by exact_mod_cast ht₂)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNR.ne'] at hh
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hu : |Real.log s + Real.log t - 2 * Real.log N| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [quadraticLogKernel, SchwartzMap.compSubConstCLM_apply, quadraticLogWindow_eq ρ _ _ hu]
  congr 1
  have he : Real.log s + Real.log t - 2 * Real.log N =
      Real.log (((s : ℝ) * t) / (N : ℝ) ^ 2) := by
    rw [Real.log_div (mul_ne_zero hsR.ne' htR.ne') (pow_ne_zero _ hNR.ne'),
      Real.log_mul hsR.ne' htR.ne', Real.log_pow]
    norm_num
  rw [he, Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

end Ostmann

end OAI
