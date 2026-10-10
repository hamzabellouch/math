import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForcedMomentum
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleOriginMomentum

namespace OAI

/-! On a ball where both scalar frequencies are nonpositive, regularity
at the origin and defocusing give nonnegative boundary momentum. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralPhysicalLiouvillePair_momentum_nonneg
    (a b eta : ℝ) (m : ℕ) (hm : 1 ≤ m) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g)
    (R : ℝ) (hR : 0 < R)
    (hF : ∀ r ∈ Ioc 0 R,
      homogeneousSpectralLocalizationFrequency 1 b eta lam.im r ≤ 0 ∧
      homogeneousSpectralLocalizationFrequency (-1) b eta lam.im r ≤ 0) :
    0 ≤ spectralPairMomentum (spectralPhysicalLiouvillePair f g R) := by
  let P := fun r => spectralPairMomentum (spectralPhysicalLiouvillePair f g r)
  have hd (r : ℝ) (hr : 0 < r) : DifferentiableAt ℝ P r :=
    spectralPhysicalLiouvillePair_momentum_differentiableAt a b eta m Q lam f g hf hg he r hr
  have hmono : MonotoneOn P (Ioc 0 R) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 R)
    · exact fun r hr => (hd r hr.1).continuousAt.continuousWithinAt
    · exact fun r hr => (hd r (interior_subset hr).1).differentiableWithinAt
    · intro r hr
      have hri := interior_subset hr
      exact spectralPhysicalLiouvillePair_momentum_deriv a b eta m hm Q lam f g hf hg he
        r hri.1 (hF r hri).1 (hF r hri).2
  have hzero : Tendsto P (𝓝[>] 0) (𝓝 0) :=
    spectralPhysicalLiouvillePair_momentum_origin f g hf hg
  have hle : ∀ᶠ r in 𝓝[>] 0, P r ≤ P R := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with r hr hrR
    exact hmono ⟨hr,hrR.le⟩ ⟨hR,le_rfl⟩ hrR.le
  exact le_of_tendsto hzero hle

end DefocusingNLS

end OAI
