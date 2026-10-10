import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedAmplitude

namespace OAI

/-! The exact nonlinear term in the amplitude/phase gauge of the spectral equation. -/

namespace DefocusingNLS
open ProfileCertificate

theorem oddPowerDerivative_gauge (m : ℕ) (Q u : ℂ) :
    oddPowerDerivative m Q (Q*u)=
      oddPowerNonlinearity m Q*(((m+1 : ℕ) : ℂ)*u+(m : ℂ)*star u) := by
  cases m with
  | zero => simp [oddPowerDerivative,oddPowerNonlinearity]
  | succ m =>
    simp only [oddPowerDerivative,add_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe,starL'_apply,smul_eq_mul,star_mul,oddPowerNonlinearity,
      Nat.succ_sub_one]
    simp only [pow_succ,Nat.cast_add,Nat.cast_one]
    ring

theorem oddPowerDerivative_gauge_real (m : ℕ) (Q : ℂ) (f g : ℝ) :
    oddPowerDerivative m Q (Q*((f : ℂ)+Complex.I*(g : ℂ)))-
      oddPowerNonlinearity m Q*((f : ℂ)+Complex.I*(g : ℂ))=
      ((2*(m : ℝ)*‖Q‖^(2*m)*f : ℝ) : ℂ)*Q := by
  rw [oddPowerDerivative_gauge,oddPowerNonlinearity_eq]
  simp only [map_add,map_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_I,
    Nat.cast_add,Nat.cast_one]
  push_cast
  ring

theorem radialMatched_gauge_pressure (n : ℕ) (z : ProfileMatchingBall) (r f g : ℝ) :
    let m := n+radialInnerShootingThreshold
    let Q := radialMatchedProfile n z r
    oddPowerDerivative m Q (Q*((f : ℂ)+Complex.I*(g : ℂ)))-
      oddPowerNonlinearity m Q*((f : ℂ)+Complex.I*(g : ℂ))=
      ((‖Q‖^(2*m)/radialShootingA n*f : ℝ) : ℂ)*Q := by
  intro m Q
  rw [oddPowerDerivative_gauge_real]
  congr 2
  unfold radialShootingA
  change 2*(m : ℝ)*‖Q‖^(2*m)*f=‖Q‖^(2*m)/(1/(2*(m : ℝ)))*f
  field_simp

end DefocusingNLS

end OAI
