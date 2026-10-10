import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularForcing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialJet
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailData

namespace OAI

/-! Bounded extensions of the approximate column and its normalized residual. -/

open scoped BoundedContinuousFunction
open Polynomial
namespace DefocusingNLS

noncomputable def boundedCircularPolynomialComponent (P : ℂ[X]) : ℝ →ᵇ ℂ × ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (boundedRadialPolynomial P t,boundedRadialPolynomial (radialPolynomialEuler P) t))
    ((boundedRadialPolynomial P).continuous.prodMk
      (boundedRadialPolynomial (radialPolynomialEuler P)).continuous)
    (max ‖boundedRadialPolynomial P‖ ‖boundedRadialPolynomial (radialPolynomialEuler P)‖)
    (fun t => max_le_max ((boundedRadialPolynomial P).norm_coe_le_norm t)
      ((boundedRadialPolynomial (radialPolynomialEuler P)).norm_coe_le_norm t))

noncomputable def boundedCircularPolynomialJet (U : ℂ[X] × ℂ[X]) : CircularTailSpace :=
  (boundedCircularPolynomialComponent U.1,boundedCircularPolynomialComponent U.2)

theorem boundedCircularPolynomialJet_eq (U : ℂ[X] × ℂ[X]) (t : ℝ) (ht : 0 ≤ t) :
    circularTailEvaluation (boundedCircularPolynomialJet U) t=circularPolynomialJet U t := by
  change ((boundedRadialPolynomial U.1 t,
    boundedRadialPolynomial (radialPolynomialEuler U.1) t),
    (boundedRadialPolynomial U.2 t,
    boundedRadialPolynomial (radialPolynomialEuler U.2) t))=circularPolynomialJet U t
  simp only [boundedRadialPolynomial_nonneg _ t ht,circularPolynomialJet]

theorem exists_circular_normalized_residual (νp νm η : ℂ) (m : ℕ)
    (P : ℂ[X]) (c : ℂ × ℂ) (j : ℕ) :
    ∃ r : CircularTailSpace, ∀ t, 0 ≤ t →
      Real.exp (-(2*(j : ℝ))*t) • circularTailEvaluation r t=
        -circularPolynomialResidualJet νp νm η m P
          (spectralOutgoingPolynomial νp νm η m P c j) t := by
  obtain ⟨R,hR⟩ := spectralOutgoingPolynomial_residual_factor νp νm η m P c j
  refine ⟨(boundedRadialResidual R.1,boundedRadialResidual R.2),?_⟩
  intro t ht
  simp only [circularTailEvaluation,boundedRadialResidual_apply,
    boundedRadialPolynomial_nonneg _ t ht,circularPolynomialResidualJet,
    Prod.smul_mk,Prod.neg_mk,smul_zero,neg_zero,Complex.real_smul,
    mul_neg,(hR t).1,(hR t).2]

end DefocusingNLS

end OAI
