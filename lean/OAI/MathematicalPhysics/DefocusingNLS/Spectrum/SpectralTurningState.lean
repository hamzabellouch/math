import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreen
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace OAI

/-! Exact Cauchy-state rescaling at a turning point. The value and derivative
factors preserve the complex flux. -/

namespace DefocusingNLS

noncomputable def spectralTurningState (r₀ d s : ℝ) (q : ℝ → ℂ × ℂ) (xi : ℝ) : ℂ × ℂ :=
  ((q (r₀+d*xi)).1/(s : ℂ),(s : ℂ)*(q (r₀+d*xi)).2)

theorem spectralTurningState_hasDerivAt
    (r₀ d s xi : ℝ) (hs : s≠0) (hsq : s^2=d) (q : ℝ → ℂ × ℂ) (V : ℂ)
    (hq : HasDerivAt q (spectralScalarField V (q (r₀+d*xi))) (r₀+d*xi)) :
    HasDerivAt (spectralTurningState r₀ d s q)
      (spectralScalarField ((d : ℂ)^2*V) (spectralTurningState r₀ d s q xi)) xi := by
  have hsC : (s : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs
  have hsqC : (s : ℂ)^2=(d : ℂ) := by exact_mod_cast hsq
  have hcomp := hq.scomp xi (((hasDerivAt_id xi).const_mul d).const_add r₀)
  have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt xi hcomp
  have h2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt xi hcomp
  apply ((h1.div_const (s : ℂ)).prodMk (h2.const_mul (s : ℂ))).congr_deriv
  apply Prod.ext
  · dsimp only [ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',Function.comp_apply,
      Prod.smul_fst,Prod.smul_snd,spectralScalarField,spectralTurningState]
    rw [Complex.real_smul]
    field_simp
    linear_combination -(q (r₀+d*xi)).2*hsqC
  · dsimp only [ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',Function.comp_apply,
      Prod.smul_fst,Prod.smul_snd,spectralScalarField,spectralTurningState]
    rw [Complex.real_smul]
    field_simp
    linear_combination -(d : ℂ)*V*(q (r₀+d*xi)).1*hsqC

theorem spectralTurningState_flux (r₀ d s xi : ℝ) (hs : s≠0) (q : ℝ → ℂ × ℂ) :
    (star (spectralTurningState r₀ d s q xi).1*(spectralTurningState r₀ d s q xi).2).im=
      (star (q (r₀+d*xi)).1*(q (r₀+d*xi)).2).im := by
  have hsC : (s : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs
  congr 1
  dsimp only [spectralTurningState]
  simp only [Complex.star_def,map_div₀,Complex.conj_ofReal]
  field_simp

end DefocusingNLS

end OAI
