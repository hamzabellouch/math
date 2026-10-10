import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansionCompatibility
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace OAI

/-! Differentiating a finite outgoing expansion preserves its order of vanishing. -/

open Polynomial Set
namespace DefocusingNLS

theorem iteratedDeriv_radialExteriorPolynomial (P : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (radialExteriorPolynomialFunction P)=
      radialExteriorPolynomialFunction ((radialPolynomialEuler^[k]) P) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    simpa only [Function.iterate_succ_apply'] using
      (radialExteriorPolynomialFunction_hasDerivAt ((radialPolynomialEuler^[k]) P) t).deriv

theorem radialPolynomialEuler_iter_dvd (P : ℂ[X]) (j k : ℕ) (hP : X^j ∣ P) :
    X^j ∣ (radialPolynomialEuler^[k]) P := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact radialPolynomialEuler_preserves_divisibility _ j ih

theorem radialExteriorPolynomial_deriv_bounded (P : ℂ[X]) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖iteratedDeriv k (radialExteriorPolynomialFunction P) t‖ ≤ C := by
  refine ⟨‖boundedRadialPolynomial ((radialPolynomialEuler^[k]) P)‖,norm_nonneg _,?_⟩
  intro t ht
  rw [iteratedDeriv_radialExteriorPolynomial,← boundedRadialPolynomial_nonneg _ t ht]
  exact (boundedRadialPolynomial ((radialPolynomialEuler^[k]) P)).norm_coe_le_norm t

theorem radialExteriorPolynomial_deriv_decay (P : ℂ[X]) (j k : ℕ) (hP : X^j ∣ P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖iteratedDeriv k (radialExteriorPolynomialFunction P) t‖ ≤
        C*Real.exp (-(2*(j : ℝ))*t) := by
  obtain ⟨R,hR⟩ := radialPolynomialEuler_iter_dvd P j k hP
  refine ⟨‖boundedRadialPolynomial R‖,norm_nonneg _,?_⟩
  intro t ht
  rw [iteratedDeriv_radialExteriorPolynomial]
  exact radialPolynomial_factor_decay _ R j hR t ht

end DefocusingNLS

end OAI
