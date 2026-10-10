import OAI.MathematicalPhysics.DefocusingNLS.Profile.CartesianTransportCalculus
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTranslationMode

namespace OAI

/-! The exact time-translation mode, from the stationary equation and homogeneity. -/

open scoped ContDiff Laplacian
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem similarityLinearization_add (a b : ℝ) (m : ℕ) (Q f g : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    similarityLinearization a b m Q (fun y => f y+g y) x=
      similarityLinearization a b m Q f x+similarityLinearization a b m Q g x := by
  have hL : Δ (fun y => f y+g y) x=Δ f x+Δ g x :=
    (hf.contDiffAt.of_le (by simp)).laplacian_add (hg.contDiffAt.of_le (by simp))
  unfold similarityLinearization
  rw [hL,fderiv_fun_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [add_apply,map_add]
  ring

theorem stationary_transport_linearization (a b : ℝ) (m : ℕ) (Q : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hstat : ∀ y, stationarySimilarityDefect a b m Q y=0)
    (x : E) :
    similarityLinearization a b m Q (cartesianTransport Q) x=Complex.I*Δ Q x := by
  have hdQ := (hQ.differentiable (by simp) x).hasFDerivAt
  have hLap := ((laplacian_contDiff Q hQ).differentiable (by simp) x).hasFDerivAt
  have hT := cartesianTransport_contDiff Q hQ
  have hN := (hasFDerivAt_oddPowerNonlinearity m (Q x)).comp x hdQ
  have hD := ((hLap.add (((hT.differentiable (by simp) x).hasFDerivAt.add
    (hdQ.const_mul (a : ℂ))).const_mul Complex.I)).add
    (hdQ.const_mul (b : ℂ))).sub hN
  change HasFDerivAt (stationarySimilarityDefect a b m Q) _ x at hD
  have he : stationarySimilarityDefect a b m Q=fun _ => 0 := funext hstat
  rw [he] at hD
  have hv := congrArg (fun L : E →L[ℝ] ℂ => L ((1/2 : ℝ) • x))
    (hD.unique (hasFDerivAt_const (0 : ℂ) x))
  simp only [add_apply,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
    zero_apply,smul_eq_mul] at hv
  change cartesianTransport (Δ Q) x+
    Complex.I*(cartesianTransport (cartesianTransport Q) x+(a : ℂ)*cartesianTransport Q x)+
    (b : ℂ)*cartesianTransport Q x-
    oddPowerDerivative m (Q x) (cartesianTransport Q x)=0 at hv
  unfold similarityLinearization
  rw [laplacian_cartesianTransport Q hQ]
  change Complex.I*(cartesianTransport (Δ Q) x+Δ Q x)-
    cartesianTransport (cartesianTransport Q) x-
    ((a : ℂ)-Complex.I*(b : ℂ))*cartesianTransport Q x-
    Complex.I*oddPowerDerivative m (Q x) (cartesianTransport Q x)=Complex.I*Δ Q x
  have hh := congrArg (fun z : ℂ => Complex.I*z) hv
  simp only [mul_add,mul_sub,← mul_assoc,Complex.I_mul_I,neg_one_mul,mul_zero] at hh
  linear_combination hh

theorem stationary_scaling_linearization (a b : ℝ) (m : ℕ) (Q : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hstat : ∀ y, stationarySimilarityDefect a b m Q y=0)
    (hma : 2*(m : ℝ)*a=1) (x : E) :
    similarityLinearization a b m Q
      (fun y => ((a : ℂ)-Complex.I*(b : ℂ))*Q y) x=
      -Complex.I*oddPowerNonlinearity m (Q x) := by
  have he : (fun y => ((a : ℂ)-Complex.I*(b : ℂ))*Q y)=
      fun y => Q y*((a : ℂ)-Complex.I*(b : ℂ)) := by
    funext y
    exact mul_comm _ _
  rw [he,similarityLinearization_gauge a b m Q _ hQ contDiff_const x (hstat x)]
  have hr : 2*(m : ℝ)*‖Q x‖^(2*m)*a=‖Q x‖^(2*m) := by
    calc
      _ = (2*(m : ℝ)*a)*‖Q x‖^(2*m) := by ring
      _ = _ := by rw [hma,one_mul]
  have hc : (a : ℂ)+Complex.I*((-b : ℝ) : ℂ)=(a : ℂ)-Complex.I*(b : ℂ) := by
    push_cast
    ring
  have hp := oddPowerDerivative_gauge_real m (Q x) a (-b)
  rw [hc] at hp
  simp only [InnerProductSpace.laplacian_const,fderiv_fun_const,Pi.zero_apply,
    zero_apply,mul_zero,sub_self,Finset.sum_const_zero,zero_add,zero_sub]
  rw [hp,hr,oddPowerNonlinearity_eq]
  push_cast
  ring

theorem stationary_time_mode (a b : ℝ) (m : ℕ) (Q : E → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hstat : ∀ y, stationarySimilarityDefect a b m Q y=0)
    (hma : 2*(m : ℝ)*a=1) (x : E) :
    let T := fun y => ((a : ℂ)-Complex.I*(b : ℂ))*Q y+cartesianTransport Q y
    similarityLinearization a b m Q T x=T x := by
  dsimp only
  rw [similarityLinearization_add a b m Q _ _ (contDiff_const.mul hQ)
    (cartesianTransport_contDiff Q hQ),stationary_scaling_linearization a b m Q hQ hstat hma,
    stationary_transport_linearization a b m Q hQ hstat]
  have hs := congrArg (fun z : ℂ => Complex.I*z) (hstat x)
  dsimp only [stationarySimilarityDefect] at hs
  simp only [mul_add,mul_sub,← mul_assoc,Complex.I_mul_I,neg_one_mul,mul_zero] at hs
  unfold cartesianTransport
  linear_combination hs

theorem radialMatched_timeMode (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (x : E) :
    let Q := radialMatchedCartesian n z
    let T := fun y => ((radialShootingA n : ℂ)-
      Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))*Q y+
        cartesianTransport Q y
    similarityLinearization (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) Q T x=T x := by
  apply stationary_time_mode _ _ _ _ (radialMatchedCartesian_contDiff n z hX hz)
    (radialMatchedCartesian_stationary n z hX hz)
  unfold radialShootingA
  have hm : (n+radialInnerShootingThreshold : ℕ)≠0 :=
    (radialShootingInner_power_pos n (profileMatchingParameter z)).ne'
  have hmc : ((n+radialInnerShootingThreshold : ℕ) : ℝ)≠0 := Nat.cast_ne_zero.mpr hm
  field_simp

end DefocusingNLS

end OAI
