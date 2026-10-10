import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledInwardMass
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMassDecay

namespace OAI

/-! An inward channel still decays when its Robin error couples to a
uniformly bounded oscillatory channel. -/

open Set
namespace DefocusingNLS

theorem spectralComplex_coupled_inward_decay (a b mu eps M : ℝ)
    (hab : a ≤ b) (hmu : 0 < mu) (heps : 0 ≤ eps) (hsmall : eps ≤ 1/2)
    (_hM : 0 ≤ M) (q dq w alpha : ℝ → ℂ)
    (hq : ContinuousOn q (Icc a b))
    (hD : ∀ r ∈ Ioo a b, HasDerivAt q (dq r) r)
    (hslope : ∀ r ∈ Ioo a b, (alpha r).re ≤ -mu)
    (herror : ∀ r ∈ Ioo a b, ‖dq r-alpha r*q r‖ ≤ eps*mu*(‖q r‖+‖w r‖))
    (hw : ∀ r ∈ Ioo a b, ‖w r‖ ≤ M) :
    Complex.normSq (q b) ≤ Real.exp (-(mu/2)*(b-a))*Complex.normSq (q a)+4*eps^2*M^2 := by
  apply spectralComplex_mass_decay a b (mu/2) (4*eps^2*M^2) hab (by positivity)
    (by positivity) q dq hq hD
  intro r hr
  have hm := spectralComplex_coupled_inward_mass (q r) (dq r) (w r) (alpha r)
    mu eps hmu heps hsmall (hslope r hr) (herror r hr)
  have hw2 : Complex.normSq (w r) ≤ M^2 := by
    rw [← Complex.sq_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hw r hr) 2
  have hc := mul_le_mul_of_nonneg_left hw2 (by positivity : 0 ≤ 2*eps^2*mu)
  nlinarith only [hm,hc]

end DefocusingNLS

end OAI
