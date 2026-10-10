import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSlowIdentification
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeConjugatePolynomial

namespace OAI

/-! The opposite circular H solution and its actual outgoing remainder. -/

open Polynomial
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialPolynomialEuler_map_star (P : ℂ[X]) :
    radialPolynomialEuler (P.map (starRingEnd ℂ))=
      (radialPolynomialEuler P).map (starRingEnd ℂ) := by
  ext k
  simp only [radialPolynomialEuler_coeff,coeff_map,map_mul,map_neg,map_natCast,map_ofNat]

theorem radialPolynomialJet_map_star (P : ℂ[X]) (t : ℝ) :
    radialPolynomialJet (P.map (starRingEnd ℂ)) t=star (radialPolynomialJet P t) := by
  have he (Q : ℂ[X]) : radialExteriorPolynomialFunction (Q.map (starRingEnd ℂ)) t=
      star (radialExteriorPolynomialFunction Q t) := by
    simpa only [radialExteriorPolynomialFunction,Complex.star_def,Complex.conj_ofReal] using
      Q.eval_map_apply (starRingEnd ℂ) (Real.exp (-2*t) : ℂ)
  simp only [radialPolynomialJet,radialPolynomialEuler_map_star,he,Prod.star_def]

noncomputable def spectralFreeSecondColumn (ell : ℕ) (q : ℂ) (t : ℝ) : E₄ :=
  (0,star (spectralFreeSlowJet (star q) (ell+6) t))

theorem spectralFreeSecondColumn_hasDerivAt (ell : ℕ) (q νp : ℂ)
    (hq : -1 < q.re) (t : ℝ) :
    HasDerivAt (spectralFreeSecondColumn ell q)
      (circularLeadingField t (spectralFreeSecondColumn ell q t)+
        circularBoundedField νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
          1 0 (spectralFreeSecondColumn ell q t)) t := by
  have hq' : -1 < (star q).re := by simpa only [Complex.star_def,Complex.conj_re] using hq
  have h := spectralFreeAngularJet_hasDerivAt ell (star q) hq' t
  have hs := HasDerivAt.star h
  have hd := (hasDerivAt_const t (0 : ℂ × ℂ)).prodMk hs
  apply hd.congr_deriv
  apply Prod.ext <;> apply Prod.ext <;>
    simp [spectralFreeSecondColumn,circularLeadingField,circularBoundedField,
      spectralDiagonalCoefficient,spectralCrossCoefficient,Prod.star_def,
      star_add,star_sub,star_mul,star_neg,Complex.conj_I,
      ← Complex.exp_conj,Complex.conj_ofReal,map_ofNat,mul_comm]
  ring

theorem spectralFreeSecondColumn_remainder (ell : ℕ) (q νp : ℂ)
    (hq : -1 < q.re) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, Real.log 4/2 ≤ t →
      ‖spectralFreeSecondColumn ell q t-circularPolynomialJet
        (spectralOutgoingPolynomial νp ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
          1 0 (0,1) (j+1)) t‖ ≤ C*Real.exp (-(2*((j+2 : ℕ) : ℝ))*t) := by
  have hq' : -1 < (star q).re := by simpa only [Complex.star_def,Complex.conj_re] using hq
  obtain ⟨C,hC,hb⟩ := spectralFreeSlowJet_remainder ell (star q) hq' j
  refine ⟨C,hC,?_⟩
  intro t ht
  rw [spectralOutgoingPolynomial_free_second]
  have hz : radialPolynomialJet (0 : ℂ[X]) t=0 := by
    simp [radialPolynomialJet,radialExteriorPolynomialFunction,radialPolynomialEuler]
  change ‖((0 : ℂ × ℂ),star (spectralFreeSlowJet (star q) (ell+6) t))-
    (radialPolynomialJet 0 t,radialPolynomialJet ((spectralFreeSlowPolynomial ell (star q) 1 (j+1)).map
      (starRingEnd ℂ)) t)‖ ≤ _
  rw [hz,radialPolynomialJet_map_star]
  rw [Prod.norm_def]
  change max ‖(0 : ℂ × ℂ)-0‖ ‖star (spectralFreeSlowJet (star q) (ell+6) t)-
    star (radialPolynomialJet (spectralFreeSlowPolynomial ell (star q) 1 (j+1)) t)‖ ≤ _
  rw [sub_self,norm_zero,← star_sub,norm_star,max_eq_right (norm_nonneg _)]
  exact hb t ht

end DefocusingNLS

end OAI
