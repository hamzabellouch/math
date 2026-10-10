import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForbiddenMomentum
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledBoundaryZero
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleStateNonzero

namespace OAI

/-! A regular nonzero defocusing eigenpair cannot have a sufficiently
accurate inward outgoing boundary condition when both channels are forbidden. -/

open Set
namespace DefocusingNLS

theorem spectralForbidden_boundary_exclusion
    (a b eta : ℝ) (m : ℕ) (hm : 1 ≤ m) (Q f g : ℝ → ℂ) (lam : ℂ)
    (hQ : ContinuousOn Q (Ioi 0)) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g)
    (hn : ∃ r : ℝ, 0 < r ∧ (f r ≠ 0 ∨ g r ≠ 0))
    (R E A : ℝ) (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ r ∈ Ioc 0 R,
      homogeneousSpectralLocalizationFrequency 1 b eta lam.im r ≤ 0 ∧
      homogeneousSpectralLocalizationFrequency (-1) b eta lam.im r ≤ 0)
    (Sp Sm : SpectralScalarBoundarySystem R E A)
    (c eps : ℝ) (hc : 0 < c) (heps : 0 ≤ eps) (hsmall : eps ≤ c/4)
    (hp : ((Sp.U R).2/(Sp.U R).1).re ≤ -c*(Sp.k R)^2)
    (hm' : ((Sm.U R).2/(Sm.U R).1).re ≤ -c*(Sm.k R)^2)
    (herr :
      let q := spectralPhysicalLiouvillePair f g R
      spectralShellPairNorm (Sp.k R) (Sm.k R)
        (q-(Sp.extension q.1.1 R,Sm.extension q.2.1 R)) ≤
        eps*max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖)) : False := by
  have hflux := spectralPhysicalLiouvillePair_momentum_nonneg a b eta m hm Q lam f g hf hg he R hR hF
  have hz := spectralCoupled_boundary_zero Sp Sm hRE c eps hc heps hsmall
    (spectralPhysicalLiouvillePair f g R) hp hm' herr hflux
  exact spectralPhysicalLiouvillePair_nonzero a b m Q f g (eta : ℂ) lam hQ hf hg he hn R hR hz

end DefocusingNLS

end OAI
