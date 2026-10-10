import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeCalculus
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicEigenmode
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OAI

/-! The physical radial eigenvalue equation conjugates to the circular gauge system. -/

namespace DefocusingNLS

theorem spectralRadialEigenpairGauge (a b : ℝ) (m : ℕ) (η lam : ℂ)
    (Q U V : ℝ → ℂ) (hQ : ContDiff ℝ 2 Q)
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (he : IsHarmonicRadialEigenpair a b m Q η lam
      (fun r => Q r*U r) (fun r => star (Q r)*V r))
    (r : ℝ) (hr : 0 < r) (hQn : Q r ≠ 0)
    (hstat : Complex.I*(deriv (deriv Q) r+11/(r : ℂ)*deriv Q r)-
      (r : ℂ)/2*deriv Q r+(-(a : ℂ)+Complex.I*(b : ℂ))*Q r-
      Complex.I*((‖Q r‖^(2*m) : ℝ) : ℂ)*Q r=0) :
    (lam*U r=Complex.I*(deriv (deriv U) r+
      (11/(r : ℂ)+2*deriv Q r/Q r)*deriv U r-η/(r : ℂ)^2*U r)-
      (r : ℂ)/2*deriv U r-
      Complex.I*(m : ℂ)*((‖Q r‖^(2*m) : ℝ) : ℂ)*(U r+V r)) ∧
    (lam*V r= -Complex.I*(deriv (deriv V) r+
      (11/(r : ℂ)+2*star (deriv Q r)/star (Q r))*deriv V r-η/(r : ℂ)^2*V r)-
      (r : ℂ)/2*deriv V r+
      Complex.I*(m : ℂ)*((‖Q r‖^(2*m) : ℝ) : ℂ)*(V r+U r)) := by
  let Qb := fun t => star (Q t)
  have hQb : ContDiff ℝ 2 Qb := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hQ
  have hprod : deriv (fun t => Q t*U t) r=deriv Q r*U r+Q r*deriv U r :=
    ((hQ.differentiable (by norm_num) r).hasDerivAt.mul
      (hU.differentiable (by norm_num) r).hasDerivAt).deriv
  have hprodb : deriv (fun t => Qb t*V t) r=deriv Qb r*V r+Qb r*deriv V r :=
    ((hQb.differentiable (by norm_num) r).hasDerivAt.mul
      (hV.differentiable (by norm_num) r).hasDerivAt).deriv
  have hstatb : -Complex.I*(deriv (deriv Qb) r+11/(r : ℂ)*deriv Qb r)-
      (r : ℂ)/2*deriv Qb r+(-(a : ℂ)-Complex.I*(b : ℂ))*star (Q r)+
      Complex.I*((‖Q r‖^(2*m) : ℝ) : ℂ)*star (Q r)=0 := by
    dsimp only [Qb]
    rw [deriv.star',deriv.star']
    have h := congrArg star hstat
    simp only [Complex.star_def,map_add,map_sub,map_mul,map_div₀,map_neg,
      Complex.conj_ofReal,Complex.conj_I,map_ofNat,map_zero] at h ⊢
    linear_combination h
  obtain ⟨hp,hm⟩ := he r hr
  rw [spectralRadialProduct_deriv_two Q U hQ hU r,hprod] at hp
  change lam*(Qb r*V r)=_ at hm
  rw [spectralRadialProduct_deriv_two Qb V hQb hV r,hprodb] at hm
  have hpalg := spectralRadialLinearizedProduct m (r : ℂ) a b η
    (Q r) (deriv Q r) (deriv (deriv Q) r) (U r) (deriv U r)
    (deriv (deriv U) r) (V r) hQn hstat
  have hmalg := spectralRadialLinearizedConjugate m (r : ℂ) a b η
    (Q r) (deriv Qb r) (deriv (deriv Qb) r) (V r) (deriv V r)
    (deriv (deriv V) r) (U r) (star_ne_zero.mpr hQn) hstatb
  push_cast at hp hm hpalg hmalg ⊢
  constructor
  · apply (mul_left_cancel₀ hQn)
    linear_combination hp+hpalg
  · have hd : deriv Qb r=star (deriv Q r) := deriv.star
    rw [hd] at hm hmalg
    apply (mul_left_cancel₀ (star_ne_zero.mpr hQn))
    change lam*(star (Q r)*V r)=_ at hm
    linear_combination hm+hmalg

end DefocusingNLS

end OAI
