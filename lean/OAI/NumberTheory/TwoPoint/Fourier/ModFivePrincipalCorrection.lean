import OAI.NumberTheory.TwoPoint.Fourier.ModFivePositivity
import Mathlib.Analysis.Calculus.LogDeriv

namespace OAI

/-! The principal modulus-five logarithmic derivative differs from the
ordinary zeta logarithmic derivative by a single, uniformly bounded Euler
factor. This is proved directly from the existing change-of-level identity.
-/

namespace TwoPointCorrelations

open Complex Filter
open scoped Classical Topology

noncomputable def modFiveEulerFactor (s : ℂ) : ℂ := 1 - (5 : ℂ) ^ (-s)

lemma modFive_principal_eq {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5) s =
      modFiveEulerFactor s * riemannZeta s := by
  have h := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 5) hs
  have hp : (5 : ℕ).primeFactors = {5} := (show Nat.Prime 5 by decide).primeFactors
  simpa only [DirichletCharacter.LFunctionTrivChar, hp, Finset.prod_singleton,
    Nat.cast_ofNat, modFiveEulerFactor] using h

lemma modFiveEulerFactor_cpow_norm {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(5 : ℂ) ^ (-s)‖ ≤ 1 / 5 := by
  change ‖((5 : ℝ) : ℂ) ^ (-s)‖ ≤ 1 / 5
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 5)]
  have he : -s.re ≤ -(1 : ℝ) := by linarith
  have hb := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) he
  norm_num at hb ⊢
  exact hb

lemma modFiveEulerFactor_norm_ge {s : ℂ} (hs : 1 ≤ s.re) :
    4 / 5 ≤ ‖modFiveEulerFactor s‖ := by
  have h := norm_sub_norm_le (1 : ℂ) ((5 : ℂ) ^ (-s))
  have hp := modFiveEulerFactor_cpow_norm hs
  simp only [norm_one] at h
  unfold modFiveEulerFactor
  linarith

lemma modFiveEulerFactor_ne_zero {s : ℂ} (hs : 1 ≤ s.re) :
    modFiveEulerFactor s ≠ 0 := by
  have h := modFiveEulerFactor_norm_ge hs
  intro heq
  rw [heq, norm_zero] at h
  norm_num at h

lemma modFiveEulerFactor_hasDeriv (s : ℂ) :
    HasDerivAt modFiveEulerFactor ((5 : ℂ) ^ (-s) * Complex.log 5) s := by
  have hp := (hasDerivAt_id s).neg.const_cpow (c := (5 : ℂ)) (Or.inl (by norm_num))
  change HasDerivAt (fun z => 1 - (5 : ℂ) ^ (-z)) _ s
  convert hp.const_sub (1 : ℂ) using 1 <;> simp

lemma modFiveEulerFactor_logderiv_norm {s : ℂ} (hs : 1 ≤ s.re) :
    ‖deriv modFiveEulerFactor s / modFiveEulerFactor s‖ ≤ Real.log 5 / 4 := by
  rw [(modFiveEulerFactor_hasDeriv s).deriv, norm_div, norm_mul]
  have hl : ‖Complex.log (5 : ℂ)‖ = Real.log 5 := by
    change ‖Complex.log ((5 : ℝ) : ℂ)‖ = Real.log 5
    rw [← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 5), Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.log_pos (by norm_num))]
  rw [hl]
  have hd := modFiveEulerFactor_norm_ge hs
  have hp := modFiveEulerFactor_cpow_norm hs
  have hlog : 0 ≤ Real.log 5 := (Real.log_pos (by norm_num)).le
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4 / 5) hd)).mpr
  nlinarith

/-- Exact principal-character correction, in logarithmic-derivative form. -/
theorem modFive_principal_logderiv {s : ℂ} (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5) s =
      deriv modFiveEulerFactor s / modFiveEulerFactor s +
        deriv riemannZeta s / riemannZeta s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have heq : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5) =ᶠ[𝓝 s]
      fun z => modFiveEulerFactor z * riemannZeta z := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    exact modFive_principal_eq hz
  have h := (logDeriv_congr_nhds heq).eq_of_nhds
  rw [logDeriv_fun_mul s (modFiveEulerFactor_ne_zero hs.le)
    (riemannZeta_ne_zero_of_one_le_re hs.le)
    (modFiveEulerFactor_hasDeriv s).differentiableAt
    (differentiableAt_riemannZeta hs1)] at h
  exact h

/-- The correction at the exceptional prime has an absolute bound. -/
theorem modFive_principal_logderiv_error {s : ℂ} (hs : 1 < s.re) :
    ‖(-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 5) s) -
      (-deriv riemannZeta s / riemannZeta s)‖ ≤ Real.log 5 / 4 := by
  simp only [neg_div]
  rw [modFive_principal_logderiv hs]
  have he : -(deriv modFiveEulerFactor s / modFiveEulerFactor s +
        deriv riemannZeta s / riemannZeta s) - -(deriv riemannZeta s / riemannZeta s) =
      -(deriv modFiveEulerFactor s / modFiveEulerFactor s) := by ring
  rw [he, norm_neg]
  exact modFiveEulerFactor_logderiv_norm hs.le

end TwoPointCorrelations

end OAI
