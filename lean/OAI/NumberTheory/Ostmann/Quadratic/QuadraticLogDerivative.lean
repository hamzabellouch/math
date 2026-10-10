import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFourierL1

namespace OAI

/-! # Explicit derivatives of the compact logarithmic Poisson cutoff -/

namespace Ostmann

open LineDeriv
open scoped SchwartzMap

noncomputable def quadraticSmoothLogCutoff : 𝓢(ℝ, ℂ) :=
  (quadraticLogBump.hasCompactSupport.comp_left
    (show Complex.ofReal 0 = 0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp quadraticLogBump.contDiff)

 theorem quadraticSmoothLogCutoff_apply (u : ℝ) :
    quadraticSmoothLogCutoff u = (quadraticLogBump u : ℂ) := rfl

noncomputable def quadraticEulerDerivative (ρ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x)
    (SchwartzMap.derivCLM ℂ ℂ ρ)

 theorem quadraticEulerDerivative_apply (ρ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticEulerDerivative ρ x = (x : ℂ) * deriv ρ x := by
  rw [quadraticEulerDerivative, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop),
    SchwartzMap.derivCLM_apply, Complex.real_smul]

 theorem quadratic_log_composition_derivative (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) :
    HasDerivAt (fun v : ℝ => ρ (X * Real.exp (-v)))
      (-quadraticEulerDerivative ρ (X * Real.exp (-u))) u := by
  have he : HasDerivAt (fun v : ℝ => X * Real.exp (-v))
      (-(X * Real.exp (-u))) u := by
    simpa only [Pi.neg_apply, id_eq, neg_mul, mul_neg, mul_one] using
      (((hasDerivAt_id u).neg.exp).const_mul X)
  have hh := (ρ.hasDerivAt (X * Real.exp (-u))).scomp u he
  simpa only [Function.comp_def, quadraticEulerDerivative_apply, Complex.real_smul,
    Complex.ofReal_neg, neg_mul] using hh

 theorem quadratic_line_derivative_one (f : 𝓢(ℝ, ℂ)) :
    ∂_{(1 : ℝ)} f = SchwartzMap.derivCLM ℂ ℂ f := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.derivCLM_apply,
    fderiv_apply_one_eq_deriv]

noncomputable def quadraticLogFirst (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) : ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff) u * ρ (X * Real.exp (-u)) -
    quadraticSmoothLogCutoff u * quadraticEulerDerivative ρ (X * Real.exp (-u))

 theorem quadraticLogWindow_hasDerivAt (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) :
    HasDerivAt (quadraticLogWindow ρ X) (quadraticLogFirst ρ X u) u := by
  have hh := (quadraticSmoothLogCutoff.hasDerivAt u).mul
    (quadratic_log_composition_derivative ρ X u)
  change HasDerivAt (fun v => quadraticSmoothLogCutoff v * ρ (X * Real.exp (-v)))
    (quadraticLogFirst ρ X u) u
  simpa only [Pi.mul_def, quadraticLogFirst,
    SchwartzMap.derivCLM_apply, quadraticSmoothLogCutoff_apply, mul_neg,
    sub_eq_add_neg] using hh

 theorem quadraticLogWindow_deriv (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) :
    (fun u => deriv (quadraticLogWindow ρ X) u) = quadraticLogFirst ρ X := by
  funext u
  exact (quadraticLogWindow_hasDerivAt ρ X u).deriv

 theorem quadraticLogWindow_second (ρ : 𝓢(ℝ, ℂ)) (X u : ℝ) :
    (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (quadraticLogWindow ρ X))) u =
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ
        quadraticSmoothLogCutoff)) u * ρ (X * Real.exp (-u)) -
      2 * (SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff) u *
        quadraticEulerDerivative ρ (X * Real.exp (-u)) +
      quadraticSmoothLogCutoff u *
        quadraticEulerDerivative (quadraticEulerDerivative ρ) (X * Real.exp (-u)) := by
  have h₁ := ((SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff).hasDerivAt u).mul
    (quadratic_log_composition_derivative ρ X u)
  have h₂ := (quadraticSmoothLogCutoff.hasDerivAt u).mul
    (quadratic_log_composition_derivative (quadraticEulerDerivative ρ) X u)
  have hh := h₁.sub h₂
  have he : HasDerivAt (quadraticLogFirst ρ X)
      ((SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ
        quadraticSmoothLogCutoff)) u * ρ (X * Real.exp (-u)) -
      2 * (SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff) u *
        quadraticEulerDerivative ρ (X * Real.exp (-u)) +
      quadraticSmoothLogCutoff u *
        quadraticEulerDerivative (quadraticEulerDerivative ρ) (X * Real.exp (-u))) u := by
    convert hh using 1
    · rfl
    · simp only [SchwartzMap.derivCLM_apply]
      ring
  rw [quadratic_line_derivative_one, quadratic_line_derivative_one,
    SchwartzMap.derivCLM_apply]
  change deriv (fun v => deriv (quadraticLogWindow ρ X) v) u = _
  rw [quadraticLogWindow_deriv]
  exact he.deriv

end Ostmann

end OAI
