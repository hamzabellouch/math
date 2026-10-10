import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteEigenpair
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIndividualOperations
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteReconstruction

namespace OAI

/-! Logarithmic bounds for the value imply those for the normalized
velocity used in the remote physical coordinates. -/

namespace DefocusingNLS

theorem spectralRemoteEulerState_symbol (sigma : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hvalue : HasLogJetBound sigma (fun t => f (Real.exp t))) :
    HasLogJetBound sigma (spectralRemoteEulerState f (deriv f)) := by
  have hnormalized : HasLogJetBound (sigma-2)
      (fun t => (Real.exp (-2*t) : ℂ)*deriv (fun s => f (Real.exp s)) t) := by
    have he : HasLogJetBound (-2) (fun t : ℝ => (Real.exp (-2*t) : ℂ)) := by
      simpa only [Complex.real_smul,mul_one] using HasLogJetBound.exponential (-2) (1 : ℂ)
    convert he.mul hvalue.deriv using 1
    ring
  have hvelocity : HasLogJetBound sigma (fun t => deriv f (Real.exp t)/(Real.exp t : ℂ)) := by
    have hh := hnormalized.mono (by linarith : sigma-2 ≤ sigma)
    convert hh using 1
    funext t
    have hd := ((hf.differentiable (by norm_num) (Real.exp t)).hasDerivAt.scomp t
      (Real.hasDerivAt_exp t)).deriv
    change deriv (fun s => f (Real.exp s)) t = _ at hd
    rw [hd]
    have he2 : (Real.exp (-2*t) : ℂ) = ((Real.exp t : ℂ)^2)⁻¹ := by
      norm_cast
      rw [← Real.exp_nat_mul,← Real.exp_neg]
      congr 1
      norm_num
    rw [he2]
    simp only [Complex.real_smul]
    field_simp
  exact hvalue.pair hvelocity

theorem spectralRemoteEigenpairState_symbol (sigma : ℝ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfv : HasLogJetBound sigma (fun t => f (Real.exp t)))
    (hgv : HasLogJetBound sigma (fun t => g (Real.exp t))) :
    HasLogJetBound sigma (spectralRemoteEigenpairState f g) :=
  (spectralRemoteEulerState_symbol sigma f hf hfv).pair
    (spectralRemoteEulerState_symbol sigma g hg hgv)

end DefocusingNLS

end OAI
