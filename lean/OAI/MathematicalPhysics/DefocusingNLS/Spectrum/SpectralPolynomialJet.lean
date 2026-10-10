import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularField
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorBoundedExpansion

namespace OAI

/-! Polynomial approximate solutions of the full two-channel spectral equation. -/

open Polynomial Filter
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def circularPolynomialJet (U : ℂ[X] × ℂ[X]) (t : ℝ) : E₄ :=
  ((radialExteriorPolynomialFunction U.1 t,
    radialExteriorPolynomialFunction (radialPolynomialEuler U.1) t),
   (radialExteriorPolynomialFunction U.2 t,
    radialExteriorPolynomialFunction (radialPolynomialEuler U.2) t))

noncomputable def circularPolynomialResidualJet (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (U : ℂ[X] × ℂ[X]) (t : ℝ) : E₄ :=
  ((0,radialExteriorPolynomialFunction (spectralPolynomialResidualPair νp νm η m P U).1 t),
   (0,radialExteriorPolynomialFunction (spectralPolynomialResidualPair νp νm η m P U).2 t))

theorem circularPolynomialJet_hasDerivAt (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (U : ℂ[X] × ℂ[X]) (t : ℝ) :
    HasDerivAt (circularPolynomialJet U)
      (circularLeadingField t (circularPolynomialJet U t)+
        circularBoundedField νp νm η m (radialExteriorPolynomialFunction P t)
          (circularPolynomialJet U t)+circularPolynomialResidualJet νp νm η m P U t) t := by
  have hp := spectralPolynomialResidual_equation 1 νp η
    (spectralDiagonalPolynomial m P) (spectralCrossPolynomial m P) U.1 U.2 t
  have hm := spectralPolynomialResidual_equation (-1) νm η
    (Polynomial.mapRingHom (starRingEnd ℂ) (spectralDiagonalPolynomial m P))
    (Polynomial.mapRingHom (starRingEnd ℂ) (spectralCrossPolynomial m P)) U.2 U.1 t
  have hs (Q : ℂ[X]) :
      radialExteriorPolynomialFunction (Polynomial.mapRingHom (starRingEnd ℂ) Q) t=
        star (radialExteriorPolynomialFunction Q t) := by
    simpa only [radialExteriorPolynomialFunction,Polynomial.coe_mapRingHom,
      Complex.star_def,Complex.conj_ofReal] using
      (Polynomial.eval_map_apply (p := Q) (starRingEnd ℂ) (Real.exp (-2*t) : ℂ))
  have hA : radialExteriorPolynomialFunction (spectralDiagonalPolynomial m P) t=
      spectralDiagonalCoefficient m (radialExteriorPolynomialFunction P t) :=
    spectralDiagonalPolynomial_eval m P (Real.exp (-2*t))
  have hB : radialExteriorPolynomialFunction (spectralCrossPolynomial m P) t=
      spectralCrossCoefficient m (radialExteriorPolynomialFunction P t) :=
    spectralCrossPolynomial_eval m P (Real.exp (-2*t))
  rw [hs,hs,hA,hB] at hm
  rw [hA,hB] at hp
  apply (((radialExteriorPolynomialFunction_hasDerivAt U.1 t).prodMk
    (radialExteriorPolynomialFunction_hasDerivAt (radialPolynomialEuler U.1) t)).prodMk
    ((radialExteriorPolynomialFunction_hasDerivAt U.2 t).prodMk
      (radialExteriorPolynomialFunction_hasDerivAt (radialPolynomialEuler U.2) t))).congr_deriv
  apply Prod.ext <;> apply Prod.ext
  · simp [circularPolynomialJet,circularLeadingField,circularBoundedField,
      circularPolynomialResidualJet]
  · simp only [circularPolynomialJet,circularLeadingField,circularBoundedField,
      circularPolynomialResidualJet,Prod.fst_add,Prod.snd_add,
      spectralPolynomialResidualPair]
    linear_combination hp
  · simp [circularPolynomialJet,circularLeadingField,circularBoundedField,
      circularPolynomialResidualJet]
  · simp only [circularPolynomialJet,circularLeadingField,circularBoundedField,
      circularPolynomialResidualJet,Prod.snd_add,
      spectralPolynomialResidualPair]
    linear_combination hm

theorem circularPolynomialJet_tendsto (U : ℂ[X] × ℂ[X]) :
    Tendsto (circularPolynomialJet U) atTop
      (nhds ((U.1.coeff 0,0),(U.2.coeff 0,0))) := by
  have hzero (P : ℂ[X]) : (radialPolynomialEuler P).coeff 0=0 := by
    simp [radialPolynomialEuler_coeff]
  unfold circularPolynomialJet
  simpa only [hzero] using
    ((radialExteriorPolynomialFunction_tendsto U.1).prodMk_nhds
      (radialExteriorPolynomialFunction_tendsto (radialPolynomialEuler U.1))).prodMk_nhds
      ((radialExteriorPolynomialFunction_tendsto U.2).prodMk_nhds
        (radialExteriorPolynomialFunction_tendsto (radialPolynomialEuler U.2)))

end DefocusingNLS

end OAI
