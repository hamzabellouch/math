import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteEulerState

namespace OAI

/-! The actual harmonic radial eigenpair satisfies the remote Euler system. -/

namespace DefocusingNLS

noncomputable def spectralRemoteEigenpairState (f g : ℝ → ℂ) (t : ℝ) : SpectralRemoteSpace :=
  (spectralRemoteEulerState f (deriv f) t,spectralRemoteEulerState g (deriv g) t)

noncomputable def spectralRemoteEulerField (a b sigma omega eta : ℝ)
    (D C : ℂ) (t : ℝ) (u : SpectralRemoteSpace) : SpectralRemoteSpace :=
  (spectralRemoteEulerChannelField 1 b a sigma omega eta D C u.2.1 t u.1,
   spectralRemoteEulerChannelField (-1) b a sigma omega eta (star D) (star C) u.1.1 t u.2)

private theorem second_projections (Y : ℝ → SpectralRemoteSpace) (Z : SpectralRemoteSpace)
    (r : ℝ) (hY : HasDerivAt Y Z r) :
    HasDerivAt (fun x => (Y x).1.2) Z.1.2 r ∧
    HasDerivAt (fun x => (Y x).2.2) Z.2.2 r := by
  have hp := (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt r hY
  have hm := (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt r hY
  constructor
  · simpa only [Function.comp_def,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] using
      (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hp
  · simpa only [Function.comp_def,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] using
      (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hm

private theorem plus_acceleration (a b eta r : ℝ) (lam x y D C w : ℂ) :
    -(11/(r : ℂ)+Complex.I*(r : ℂ)/2)*y-
      (-Complex.I*(-2*(a : ℂ)+2*Complex.I*(b : ℂ)-2*lam)/2-(eta : ℂ)/(r : ℂ)^2)*x+D*x+C*w =
    -(11/(r : ℂ)+(1 : ℂ)*Complex.I*(r : ℂ)/2)*y+
      (-(b : ℂ)-(1 : ℂ)*Complex.I*((a : ℂ)+(lam.re : ℂ)+Complex.I*(lam.im : ℂ))+
        (eta : ℂ)/(r : ℂ)^2)*x+D*x+C*w := by
  have hl : lam = (lam.re : ℂ)+Complex.I*(lam.im : ℂ) := by
    rw [mul_comm]; exact (Complex.re_add_im lam).symm
  conv_lhs => rw [hl]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem minus_acceleration (a b eta r : ℝ) (lam x y D C w : ℂ) :
    -(11/(r : ℂ)-Complex.I*(r : ℂ)/2)*y-
      (Complex.I*(-2*(a : ℂ)-2*Complex.I*(b : ℂ)-2*lam)/2-(eta : ℂ)/(r : ℂ)^2)*x+D*x+C*w =
    -(11/(r : ℂ)+(-1 : ℂ)*Complex.I*(r : ℂ)/2)*y+
      (-(b : ℂ)-(-1 : ℂ)*Complex.I*((a : ℂ)+(lam.re : ℂ)+Complex.I*(lam.im : ℂ))+
        (eta : ℂ)/(r : ℂ)^2)*x+D*x+C*w := by
  have hl : lam = (lam.re : ℂ)+Complex.I*(lam.im : ℂ) := by
    rw [mul_comm]; exact (Complex.re_add_im lam).symm
  conv_lhs => rw [hl]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem spectralRemoteEigenpair_accelerations
    (a b eta : ℝ) (m : ℕ) (Q f g : ℝ → ℂ) (lam : ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g) (t : ℝ) :
    let r := Real.exp t
    HasDerivAt (deriv f)
      (-(11/(r : ℂ)+(1 : ℂ)*Complex.I*(r : ℂ)/2)*deriv f r+
        (-(b : ℂ)-(1 : ℂ)*Complex.I*((a : ℂ)+(lam.re : ℂ)+Complex.I*(lam.im : ℂ))+
          (eta : ℂ)/(r : ℂ)^2)*f r+
          spectralDiagonalCoefficient m (Q r)*f r+spectralCrossCoefficient m (Q r)*g r) r ∧
    HasDerivAt (deriv g)
      (-(11/(r : ℂ)+(-1 : ℂ)*Complex.I*(r : ℂ)/2)*deriv g r+
        (-(b : ℂ)-(-1 : ℂ)*Complex.I*((a : ℂ)+(lam.re : ℂ)+Complex.I*(lam.im : ℂ))+
          (eta : ℂ)/(r : ℂ)^2)*g r+
          star (spectralDiagonalCoefficient m (Q r))*g r+
          star (spectralCrossCoefficient m (Q r))*f r) r := by

  let r := Real.exp t
  have hr : 0 < r := Real.exp_pos t
  have hd := harmonicRadialState_hasDerivAt a b m Q f g (eta : ℂ) lam hf hg he r hr
  have hpf : HasDerivAt f (deriv f r) r := (hf.differentiable (by norm_num) r).hasDerivAt
  have hpg : HasDerivAt g (deriv g r) r := (hg.differentiable (by norm_num) r).hasDerivAt
  obtain ⟨hpd,hmd⟩ := second_projections _ _ r hd
  have hp' : HasDerivAt (deriv f)
      (-(11/(r : ℂ)+(1 : ℂ)*Complex.I*(r : ℂ)/2)*deriv f r+
        (-(b : ℂ)-(1 : ℂ)*Complex.I*((a : ℂ)+(lam.re : ℂ)+Complex.I*(lam.im : ℂ))+
          (eta : ℂ)/(r : ℂ)^2)*f r+
          spectralDiagonalCoefficient m (Q r)*f r+spectralCrossCoefficient m (Q r)*g r) r := by
    apply hpd.congr_deriv
    exact plus_acceleration a b eta r lam _ _ _ _ _
  have hm' : HasDerivAt (deriv g)
      (-(11/(r : ℂ)+(-1 : ℂ)*Complex.I*(r : ℂ)/2)*deriv g r+
        (-(b : ℂ)-(-1 : ℂ)*Complex.I*((a : ℂ)+(lam.re : ℂ)+Complex.I*(lam.im : ℂ))+
          (eta : ℂ)/(r : ℂ)^2)*g r+
          star (spectralDiagonalCoefficient m (Q r))*g r+
          star (spectralCrossCoefficient m (Q r))*f r) r := by
    apply hmd.congr_deriv
    exact minus_acceleration a b eta r lam _ _ _ _ _
  exact ⟨hp',hm'⟩

theorem spectralRemoteEigenpair_plus
    (a b eta : ℝ) (m : ℕ) (Q f g : ℝ → ℂ) (lam : ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g) (t : ℝ) :
    HasDerivAt (spectralRemoteEulerState f (deriv f))
      (spectralRemoteEulerChannelField 1 b a lam.re lam.im eta
        (spectralDiagonalCoefficient m (Q (Real.exp t)))
        (spectralCrossCoefficient m (Q (Real.exp t))) (g (Real.exp t)) t
        (spectralRemoteEulerState f (deriv f) t)) t := by
  have hd := (hf.differentiable (by norm_num) (Real.exp t)).hasDerivAt
  have ha := (spectralRemoteEigenpair_accelerations a b eta m Q f g lam hf hg he t).1
  exact spectralRemoteEulerState_equation f (deriv f) t 1 b a lam.re lam.im eta
    (spectralDiagonalCoefficient m (Q (Real.exp t)))
    (spectralCrossCoefficient m (Q (Real.exp t))) (g (Real.exp t)) hd ha

theorem spectralRemoteEigenpair_minus
    (a b eta : ℝ) (m : ℕ) (Q f g : ℝ → ℂ) (lam : ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g) (t : ℝ) :
    HasDerivAt (spectralRemoteEulerState g (deriv g))
      (spectralRemoteEulerChannelField (-1) b a lam.re lam.im eta
        (star (spectralDiagonalCoefficient m (Q (Real.exp t))))
        (star (spectralCrossCoefficient m (Q (Real.exp t)))) (f (Real.exp t)) t
        (spectralRemoteEulerState g (deriv g) t)) t := by
  have hd := (hg.differentiable (by norm_num) (Real.exp t)).hasDerivAt
  have ha := (spectralRemoteEigenpair_accelerations a b eta m Q f g lam hf hg he t).2
  exact spectralRemoteEulerState_equation g (deriv g) t (-1) b a lam.re lam.im eta
    (star (spectralDiagonalCoefficient m (Q (Real.exp t))))
    (star (spectralCrossCoefficient m (Q (Real.exp t)))) (f (Real.exp t)) hd
      (by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using ha)

theorem spectralRemoteEigenpairState_hasDerivAt
    (a b eta : ℝ) (m : ℕ) (Q f g : ℝ → ℂ) (lam : ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g) (t : ℝ) :
    HasDerivAt (spectralRemoteEigenpairState f g)
      (spectralRemoteEulerField a b lam.re lam.im eta
        (spectralDiagonalCoefficient m (Q (Real.exp t)))
        (spectralCrossCoefficient m (Q (Real.exp t))) t
        (spectralRemoteEigenpairState f g t)) t := by
  exact (spectralRemoteEigenpair_plus a b eta m Q f g lam hf hg he t).prodMk
    (spectralRemoteEigenpair_minus a b eta m Q f g lam hf hg he t)

end DefocusingNLS

end OAI
