import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteRootReduction
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicSmoothness

namespace OAI

/-! Exact logarithmic coordinates used by the remote block reduction. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def spectralRemoteEulerState (f g : ℝ → ℂ) (t : ℝ) : ℂ × ℂ :=
  (f (Real.exp t),g (Real.exp t)/(Real.exp t : ℂ))

theorem spectralRemoteEulerState_hasDerivAt
    (f g : ℝ → ℂ) (t : ℝ) (z : ℂ)
    (hf : HasDerivAt f (g (Real.exp t)) (Real.exp t))
    (hg : HasDerivAt g z (Real.exp t)) :
    HasDerivAt (spectralRemoteEulerState f g)
      ((Real.exp t : ℂ)*g (Real.exp t),z-g (Real.exp t)/(Real.exp t : ℂ)) t := by
  have he := Real.hasDerivAt_exp t
  have hr := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t he
  have hgf := hg.scomp t he
  have hq := hgf.div hr (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne')
  have hp := (hf.scomp t he).prodMk hq
  apply hp.congr_deriv
  apply Prod.ext
  · simp only [Complex.real_smul,mul_comm]
  · simp only [Complex.ofRealCLM_apply,Complex.real_smul,Function.comp_apply]
    field_simp

noncomputable def spectralRemoteEulerChannelField
    (h b a sigma omega eta : ℝ) (D C v : ℂ) (t : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  let c := h*omega*Real.exp (-2*t)+eta*Real.exp (-4*t)
  ((Real.exp t : ℂ)^2*u.2,
    (Real.exp t : ℂ)^2*((c : ℂ)*u.1-(h : ℂ)*Complex.I/2*u.2)+
      (-12*u.2+(-(b : ℂ)-(h : ℂ)*Complex.I*((a : ℂ)+(sigma : ℂ))+D)*u.1+C*v))

theorem spectralRemoteEulerState_equation
    (f g : ℝ → ℂ) (t h b a sigma omega eta : ℝ) (D C v : ℂ)
    (hf : HasDerivAt f (g (Real.exp t)) (Real.exp t))
    (hg : HasDerivAt g
      (-(11/(Real.exp t : ℂ)+(h : ℂ)*Complex.I*(Real.exp t : ℂ)/2)*g (Real.exp t)+
        (-(b : ℂ)-(h : ℂ)*Complex.I*((a : ℂ)+(sigma : ℂ)+Complex.I*(omega : ℂ))+
          (eta : ℂ)/(Real.exp t : ℂ)^2)*f (Real.exp t)+D*f (Real.exp t)+C*v)
      (Real.exp t)) :
    HasDerivAt (spectralRemoteEulerState f g)
      (spectralRemoteEulerChannelField h b a sigma omega eta D C v t
        (spectralRemoteEulerState f g t)) t := by
  dsimp only [spectralRemoteEulerChannelField]
  have hp := spectralRemoteEulerState_hasDerivAt f g t _ hf hg
  have he2 : (Real.exp (-2*t) : ℂ) = ((Real.exp t : ℂ)^2)⁻¹ := by
    norm_cast
    rw [← Real.exp_nat_mul,← Real.exp_neg]
    congr 1
    norm_num
  have he4 : (Real.exp (-4*t) : ℂ) = ((Real.exp t : ℂ)^4)⁻¹ := by
    norm_cast
    rw [← Real.exp_nat_mul,← Real.exp_neg]
    congr 1
    norm_num
  apply hp.congr_deriv
  apply Prod.ext
  · dsimp only [spectralRemoteEulerState]
    field_simp
  · dsimp only [spectralRemoteEulerState]
    simp only [Complex.ofReal_add,Complex.ofReal_mul]
    rw [he2,he4]
    have hr : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
    field_simp [hr]
    ring_nf
    simp only [Complex.I_sq]
    ring

end DefocusingNLS

end OAI
