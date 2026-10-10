import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import OAI.NumberTheory.SiegelZeros.Determinants.NormalizedCompletion
import OAI.NumberTheory.SiegelZeros.EntireFunctions.GammaBound

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W52
open Complex
open scoped Topology Classical

private theorem re_half_pos {s : ℂ} (hs : 0 < s.re) : 0 < (s / 2).re := by
  simpa only [Complex.div_ofNat_re] using half_pos hs

theorem hasDerivAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Complex.Gammaℝ
      (((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) *
        Complex.Gamma (s / 2) +
        (Real.pi : ℂ) ^ (-s / 2) * (deriv Complex.Gamma (s / 2) * (1 / 2))) s := by
  have hp := ((hasDerivAt_id s).neg.div_const (2 : ℂ)).const_cpow
    (Or.inl (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero))
  have hg := ((analyticAt_Gamma_of_re_pos (re_half_pos hs)).differentiableAt.hasDerivAt).comp s ((hasDerivAt_id s).div_const (2 : ℂ))
  exact hp.mul hg

theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -Complex.log (Real.pi : ℂ) / 2 + gammaLogDerivative (s / 2) / 2 := by
  have hp : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have hg : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (re_half_pos hs)
  rw [logDeriv_apply, (hasDerivAt_Gammaℝ hs).deriv, Complex.Gammaℝ_def,
    gammaLogDerivative]
  field_simp [hp, hg]

theorem logDeriv_shifted_Gammaℝ {s a : ℂ} (hs : 0 < (s + a).re) :
    logDeriv (fun z : ℂ => Complex.Gammaℝ (z + a)) s =
      -Complex.log (Real.pi : ℂ) / 2 + gammaLogDerivative ((s + a) / 2) / 2 := by
  have hd := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + a)
    (x := s) (hasDerivAt_Gammaℝ hs).differentiableAt
    (differentiableAt_id.add_const a)
  simpa only [Function.comp_def, deriv_id'', deriv_add_const, mul_one,
    logDeriv_Gammaℝ hs] using hd

variable {q : ℕ}

theorem differentiableAt_gammaFactor (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact (hasDerivAt_Gammaℝ hs).differentiableAt
  · have hp : 0 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
    exact ((hasDerivAt_Gammaℝ hp).comp s ((hasDerivAt_id s).add_const 1)).differentiableAt

theorem logDeriv_gammaFactor (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (DirichletCharacter.gammaFactor χ) s =
      -Complex.log (Real.pi : ℂ) / 2 +
      gammaLogDerivative ((s + if χ.Even then (0 : ℂ) else 1) / 2) / 2 := by
  by_cases hχ : χ.Even
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext z
      simp only [DirichletCharacter.gammaFactor, hχ, ite_true]
    rw [hfun]
    simpa only [hχ, ite_true, add_zero] using (logDeriv_Gammaℝ hs)
  · have hp : 0 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
    have hfun : DirichletCharacter.gammaFactor χ =
        (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z
      simp only [DirichletCharacter.gammaFactor, hχ, ite_false]
    rw [hfun]
    simpa only [hχ, ite_false] using (logDeriv_shifted_Gammaℝ (s := s) (a := 1) hp)

variable [NeZero q]

theorem logDeriv_LFunction_eq_completed_sub (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv χ.LFunction s = logDeriv (DirichletCharacter.completedLFunction χ) s -
      logDeriv (DirichletCharacter.gammaFactor χ) s := by
  have hp : 0 < s.re := lt_trans zero_lt_one hs
  have hne : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro hz
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
      ((W03.LFunction_zero_iff_completed_zero χ hp).mpr hz)
  have he : χ.LFunction =ᶠ[𝓝 s]
      (fun z => DirichletCharacter.completedLFunction χ z / DirichletCharacter.gammaFactor χ z) := by
    have hn : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp
    filter_upwards [hn] with z hz
    apply DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z
    left
    intro heq
    simp [heq] at hz
  rw [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
  change logDeriv (fun z => DirichletCharacter.completedLFunction χ z /
    DirichletCharacter.gammaFactor χ z) s = _
  exact logDeriv_div s hne (W03.gammaFactor_ne_zero_of_re_pos χ hp)
    (DirichletCharacter.differentiable_completedLFunction hχ s)
    (differentiableAt_gammaFactor χ hp)

theorem logDeriv_normalizedCompletion_eq (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (W51.normalizedCompletion χ) s =
      Complex.log (q : ℂ) / 2 - Complex.log (Real.pi : ℂ) / 2 +
      gammaLogDerivative ((s + if χ.Even then (0 : ℂ) else 1) / 2) / 2 +
      logDeriv χ.LFunction s := by
  have hp : 0 < s.re := lt_trans zero_lt_one hs
  have hne : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro hz
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
      ((W03.LFunction_zero_iff_completed_zero χ hp).mpr hz)
  rw [W51.logDeriv_normalizedCompletion χ hχ hne]
  have h := logDeriv_LFunction_eq_completed_sub χ hχ hs
  rw [logDeriv_gammaFactor χ hp] at h
  linear_combination -h

end SiegelZerosAwei.W52

end

end SiegelZeros

end OAI
