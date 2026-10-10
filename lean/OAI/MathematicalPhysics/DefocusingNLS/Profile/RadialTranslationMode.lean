import OAI.MathematicalPhysics.DefocusingNLS.Profile.CartesianDirectionalCalculus
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGaugeLinearization

namespace OAI

/-! The translation eigenvectors of the exact finite-power similarity generator. -/

open scoped ContDiff Laplacian
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem stationary_translation_mode (a b : ℝ) (m : ℕ) (Q : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hstat : ∀ y, stationarySimilarityDefect a b m Q y=0)
    (v x : E) :
    similarityLinearization a b m Q (cartesianDerivative v Q) x=
      (1/2 : ℂ)*cartesianDerivative v Q x := by
  have hdQ := (hQ.differentiable (by simp) x).hasFDerivAt
  have hLap := ((laplacian_contDiff Q hQ).differentiable (by simp) x).hasFDerivAt
  have hT : ContDiff ℝ ∞ (fun y => fderiv ℝ Q y ((1/2 : ℝ) • y)) :=
    (contDiff_infty_iff_fderiv.mp hQ).2.clm_apply (contDiff_id.const_smul (1/2 : ℝ))
  have hN := (hasFDerivAt_oddPowerNonlinearity m (Q x)).comp x hdQ
  have hD := ((hLap.add (((hT.differentiable (by simp) x).hasFDerivAt.add
    (hdQ.const_mul (a : ℂ))).const_mul Complex.I)).add
    (hdQ.const_mul (b : ℂ))).sub hN
  change HasFDerivAt (stationarySimilarityDefect a b m Q) _ x at hD
  have he : stationarySimilarityDefect a b m Q=fun _ => 0 := funext hstat
  rw [he] at hD
  have hv := congrArg (fun L : E →L[ℝ] ℂ => L v)
    (hD.unique (hasFDerivAt_const (0 : ℂ) x))
  simp only [add_apply,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
    zero_apply,smul_eq_mul] at hv
  have hL : fderiv ℝ (Δ Q) x v=Δ (cartesianDerivative v Q) x :=
    congrFun (laplacian_cartesianDerivative Q hQ v).symm x
  rw [hL,cartesianDerivative_transport Q hQ x v] at hv
  change Δ (cartesianDerivative v Q) x+
    Complex.I*(fderiv ℝ (cartesianDerivative v Q) x ((1/2 : ℝ) • x)+
      (1/2 : ℂ)*cartesianDerivative v Q x+(a : ℂ)*cartesianDerivative v Q x)+
    (b : ℂ)*cartesianDerivative v Q x-
    oddPowerDerivative m (Q x) (cartesianDerivative v Q x)=0 at hv
  have hh := congrArg (fun z : ℂ => Complex.I*z) hv
  simp only [mul_add,mul_sub,← mul_assoc,Complex.I_mul_I,neg_one_mul,mul_zero] at hh
  unfold similarityLinearization
  linear_combination hh

theorem radialMatched_translationMode (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (v x : E) :
    similarityLinearization (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) (radialMatchedCartesian n z)
      (cartesianDerivative v (radialMatchedCartesian n z)) x=
        (1/2 : ℂ)*cartesianDerivative v (radialMatchedCartesian n z) x :=
  stationary_translation_mode _ _ _ _ (radialMatchedCartesian_contDiff n z hX hz)
    (radialMatchedCartesian_stationary n z hX hz) v x

end DefocusingNLS

end OAI
