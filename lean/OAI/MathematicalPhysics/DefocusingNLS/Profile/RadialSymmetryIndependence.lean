import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTimeMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhaseMode

namespace OAI

/-! Nonvanishing of the time mode and independence of the two radial symmetries. -/

open scoped ContDiff Laplacian
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialShootingA_positive (n : ℕ) (z : ProfileMatchingBall) :
    0 < radialShootingA n := by
  unfold radialShootingA
  exact one_div_pos.mpr (mul_pos (by norm_num)
    (Nat.cast_pos.mpr (radialShootingInner_power_pos n (profileMatchingParameter z))))

theorem radialMatched_timeMode_at_zero (n : ℕ) (z : ProfileMatchingBall) :
    ((radialShootingA n : ℂ)-Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))*
      radialMatchedCartesian n z 0+cartesianTransport (radialMatchedCartesian n z) 0=
    ((radialShootingA n : ℂ)-Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))*
      radialMatchedCartesian n z 0 := by
  simp [cartesianTransport]

theorem radialMatched_timeMode_ne_zero (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) :
    ((radialShootingA n : ℂ)-Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))*
      radialMatchedCartesian n z 0+cartesianTransport (radialMatchedCartesian n z) 0≠0 := by
  rw [radialMatched_timeMode_at_zero]
  apply mul_ne_zero
  · intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Complex.zero_re] at hr
    exact (radialShootingA_positive n z).ne' hr
  · simpa only [radialMatchedCartesian,norm_zero] using radialMatchedProfile_ne_zero n z hX 0 le_rfl

theorem radialMatched_radialSymmetries_independent (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (s t : ℝ)
    (h : ∀ x : E, (s : ℂ)*(Complex.I*radialMatchedCartesian n z x)+
      (t : ℂ)*(((radialShootingA n : ℂ)-
        Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))*
          radialMatchedCartesian n z x+cartesianTransport (radialMatchedCartesian n z) x)=0) :
    s=0 ∧ t=0 := by
  have h0 := h 0
  rw [radialMatched_timeMode_at_zero] at h0
  have hq : radialMatchedCartesian n z 0≠0 := by
    simpa only [radialMatchedCartesian,norm_zero] using radialMatchedProfile_ne_zero n z hX 0 le_rfl
  have hc : (s : ℂ)*Complex.I+(t : ℂ)*((radialShootingA n : ℂ)-
      Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ))=0 := by
    apply (mul_eq_zero.mp (show ((s : ℂ)*Complex.I+(t : ℂ)*((radialShootingA n : ℂ)-
      Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)))*
        radialMatchedCartesian n z 0=0 by linear_combination h0)).resolve_right hq
  have hr := congrArg Complex.re hc
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.sub_re,Complex.sub_im,zero_mul,mul_zero,
    sub_zero,zero_sub,zero_add,Complex.zero_re] at hr
  have ht : t=0 := (mul_eq_zero.mp hr).resolve_right (radialShootingA_positive n z).ne'
  subst t
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at hc
  have hs : s=0 := by simpa using congrArg Complex.im hc
  exact ⟨hs,rfl⟩

end DefocusingNLS

end OAI
