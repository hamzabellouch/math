import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellForcingContinuity

namespace OAI

/-! The actual eigenpair inherits the no-turn shell energy estimate; its
coefficient equation and forcing continuity are discharged internally. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralPhysicalLiouvillePair_oscillatory_energy
    (a beta eta : ℝ) (m : ℕ) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a beta m Q (eta : ℂ) lam f g)
    (hQ : ContinuousOn Q (Ioi 0)) (C R r₀ r₁ : ℝ)
    (hbeta : 0 ≤ beta) (heta : 0 ≤ eta) (hw : 2 ≤ lam.im)
    (hgamma : |a+lam.re-3| ≤ 8) (hC : 0 ≤ C) (hR : 0 < R)
    (hRr : R ≤ r₀) (hrr : r₀ ≤ r₁)
    (hL : eta+99/4 ≤ C*lam.im) (hCR : 2*C ≤ R^2) :
    let q := spectralPhysicalLiouvillePair f g
    let F := homogeneousSpectralLocalizationFrequency (-1) beta eta lam.im
    ∀ r ∈ Icc r₀ r₁,
      spectralOscillatoryEnergy (F r) (q r).2 ≤
      (spectralOscillatoryEnergy (F r₀) (q r₀).2+
        ∫ t in r₀..r₁, ‖spectralShellMinusForcing m (Q t) t (q t)‖^2)*
          Real.exp ((2/R+4*C/R^3+17)*(r-r₀)) := by
  let q := spectralPhysicalLiouvillePair f g
  have hr₀ : 0 < r₀ := hR.trans_le hRr
  have hsub : Icc r₀ r₁ ⊆ Ioi 0 := fun r hr => hr₀.trans_le hr.1
  have hqc : ContinuousOn q (Icc r₀ r₁) :=
    (spectralPhysicalLiouvillePair_continuousOn a beta eta m Q lam f g hf hg he).mono hsub
  have hforcing := (spectralShellForcing_continuousOn m r₀ r₁ hr₀ Q q (hQ.mono hsub) hqc).2
  exact spectralNoTurn_energy_propagation beta eta lam.im (-(a+lam.re-3)) C R r₀ r₁
    hbeta heta hw (by simpa only [abs_neg] using hgamma) hC hR hRr hrr hL hCR
    (fun r => (q r).2) (fun r => spectralShellMinusForcing m (Q r) r (q r)) hqc.snd hforcing
    (fun r hr => (spectralPhysicalLiouvillePair_equation a beta eta m Q lam f g hf hg he r (hsub hr)).2)

end DefocusingNLS

end OAI
