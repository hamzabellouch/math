import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGaugeNonlinearity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianEquation

namespace OAI

/-! Exact conjugation of the similarity linearization by its stationary profile.

These are pointwise identities for the actual differential expression.  They
supply the cancellation used in `spectrum.tex`, equation (spec:real-system).
-/

open scoped ContDiff Laplacian
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def similarityLinearization (a b : ℝ) (m : ℕ)
    (Q v : E → ℂ) (x : E) : ℂ :=
  Complex.I * Δ v x - fderiv ℝ v x ((1/2 : ℝ) • x) -
    ((a : ℂ)-Complex.I*(b : ℂ))*v x - Complex.I*oddPowerDerivative m (Q x) (v x)

theorem similarityLinearization_gauge (a b : ℝ) (m : ℕ) (Q u : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hu : ContDiff ℝ ∞ u) (x : E)
    (hs : stationarySimilarityDefect a b m Q x=0) :
    similarityLinearization a b m Q (fun y => Q y*u y) x =
      Q x*(Complex.I*Δ u x-fderiv ℝ u x ((1/2 : ℝ) • x))+
      2*Complex.I*∑ j : Fin 12,
        fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)*
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j)-
      Complex.I*(oddPowerDerivative m (Q x) (Q x*u x)-
        oddPowerNonlinearity m (Q x)*u x) := by
  have hd : fderiv ℝ (fun y => Q y*u y) x ((1/2 : ℝ) • x)=
      Q x*fderiv ℝ u x ((1/2 : ℝ) • x)+
        u x*fderiv ℝ Q x ((1/2 : ℝ) • x) := by
    rw [fderiv_fun_mul (hQ.differentiable (by simp) x) (hu.differentiable (by simp) x)]
    simp only [add_apply,smul_apply,smul_eq_mul]
  have hc := congrArg (fun z : ℂ => Complex.I*z) hs
  dsimp only [stationarySimilarityDefect] at hc
  simp only [mul_add,mul_sub,← mul_assoc,Complex.I_mul_I,neg_one_mul,mul_zero] at hc
  unfold similarityLinearization
  rw [laplacian_complex_mul Q u hQ hu,hd]
  linear_combination u x*hc

/-- Division of the gradient by the nonvanishing profile is the only
coefficient introduced by the gauge. -/
theorem similarityLinearization_logGauge (a b : ℝ) (m : ℕ) (Q u : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hu : ContDiff ℝ ∞ u) (x : E)
    (hs : stationarySimilarityDefect a b m Q x=0) (hne : Q x≠0) :
    similarityLinearization a b m Q (fun y => Q y*u y) x =
      Q x*(Complex.I*Δ u x-fderiv ℝ u x ((1/2 : ℝ) • x)+
        2*Complex.I*∑ j : Fin 12,
          (fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x)*
            fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j))-
      Complex.I*(oddPowerDerivative m (Q x) (Q x*u x)-
        oddPowerNonlinearity m (Q x)*u x) := by
  rw [similarityLinearization_gauge a b m Q u hQ hu x hs]
  have he : Q x*(∑ j : Fin 12,
      (fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x)*
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j))=
      ∑ j : Fin 12, fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)*
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  linear_combination -2*Complex.I*he

theorem radialMatched_similarityLinearization (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (x : E) :
    let Q := radialMatchedCartesian n z
    similarityLinearization (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) Q (fun y => Q y*u y) x =
      Q x*(Complex.I*Δ u x-fderiv ℝ u x ((1/2 : ℝ) • x)+
        2*Complex.I*∑ j : Fin 12,
          (fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x)*
            fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j))-
      Complex.I*(oddPowerDerivative (n+radialInnerShootingThreshold) (Q x) (Q x*u x)-
        oddPowerNonlinearity (n+radialInnerShootingThreshold) (Q x)*u x) := by
  intro Q
  exact similarityLinearization_logGauge _ _ _ Q u
    (radialMatchedCartesian_contDiff n z hX hz) hu x
    (radialMatchedCartesian_stationary n z hX hz x)
    (radialMatchedProfile_ne_zero n z hX ‖x‖ (norm_nonneg x))

/-- The complexification of the weighted scalar Laplace expression. -/
noncomputable def gaugeWeightedLaplacian (Q u : E → ℂ) (x : E) : ℂ :=
  Δ u x+2*∑ j : Fin 12,
    (((fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x).re : ℝ) : ℂ)*
      fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j)

/-- The complexification of the real transport expression in the profile gauge. -/
noncomputable def gaugeTransport (Q u : E → ℂ) (x : E) : ℂ :=
  fderiv ℝ u x ((1/2 : ℝ) • x)+2*∑ j : Fin 12,
    (((fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x).im : ℝ) : ℂ)*
      fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j)

theorem similarityLinearization_splitGauge (a b : ℝ) (m : ℕ) (Q u : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hu : ContDiff ℝ ∞ u) (x : E)
    (hs : stationarySimilarityDefect a b m Q x=0) (hne : Q x≠0) :
    similarityLinearization a b m Q (fun y => Q y*u y) x =
      Q x*(Complex.I*gaugeWeightedLaplacian Q u x-gaugeTransport Q u x-
        Complex.I*((2*(m : ℝ)*‖Q x‖^(2*m)*(u x).re : ℝ) : ℂ)) := by
  rw [similarityLinearization_logGauge a b m Q u hQ hu x hs hne]
  have hrep : ((u x).re : ℂ)+Complex.I*((u x).im : ℂ)=u x := by
    apply Complex.ext <;> simp
  have hp := oddPowerDerivative_gauge_real m (Q x) (u x).re (u x).im
  rw [hrep] at hp
  rw [hp]
  have he : (∑ j : Fin 12,
      (fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x)*
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j))=
      (∑ j : Fin 12,
        (((fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x).re : ℝ) : ℂ)*
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j))+
      Complex.I*∑ j : Fin 12,
        (((fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x).im : ℝ) : ℂ)*
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hz : (((fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x).re : ℝ) : ℂ)+
        Complex.I*(((fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x).im : ℝ) : ℂ)=
        fderiv ℝ Q x (EuclideanSpace.basisFun (Fin 12) ℝ j)/Q x := by
      apply Complex.ext <;> simp
    calc
      _ = _ := congrArg (fun z : ℂ => z * fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j)) hz.symm
      _ = _ := by ring
  have halg (q d t r j v : ℂ) :
      q*(Complex.I*d-t+2*Complex.I*(r+Complex.I*j))-Complex.I*(v*q)=
        q*(Complex.I*(d+2*r)-(t+2*j)-Complex.I*v) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [he]
  exact halg _ _ _ _ _ _

theorem radialMatched_splitGauge (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (x : E) :
    let Q := radialMatchedCartesian n z
    similarityLinearization (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) Q (fun y => Q y*u y) x =
      Q x*(Complex.I*gaugeWeightedLaplacian Q u x-gaugeTransport Q u x-
        Complex.I*((‖Q x‖^(2*(n+radialInnerShootingThreshold))/radialShootingA n*
          (u x).re : ℝ) : ℂ)) := by
  intro Q
  rw [similarityLinearization_splitGauge _ _ _ Q u
    (radialMatchedCartesian_contDiff n z hX hz) hu x
    (radialMatchedCartesian_stationary n z hX hz x)
    (radialMatchedProfile_ne_zero n z hX ‖x‖ (norm_nonneg x))]
  have he : 2*((n+radialInnerShootingThreshold : ℕ) : ℝ)*
      ‖Q x‖^(2*(n+radialInnerShootingThreshold))*(u x).re=
      ‖Q x‖^(2*(n+radialInnerShootingThreshold))/radialShootingA n*(u x).re := by
    unfold radialShootingA
    field_simp
  rw [he]

end DefocusingNLS

end OAI
