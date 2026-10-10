import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactJordanPositive
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactSpectralClassification

namespace OAI

/-! No radial Jordan pair survives on a fixed compact set in the counting half-plane. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_no_jordan_compact (hRou : RectangleRouche)
    (ell N : ℕ) (hN : 7≤N) (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ lam ∈ K, -(1/32 : ℝ)≤lam.re →
      ¬ HasRadialJordanMode n z ell N lam := by
  filter_upwards [radialMatched_no_jordan_compact_nonnegative hRou ell N hN K hK,
    radialMatchedSpectralMode_compact_classification hRou ell N hN K hK] with n hn hc
  intro z hX hm lam hl hh hj
  have hsym := hc z hX hm lam hl hh hj.radialMode
  have hnonneg : 0≤lam.re := by
    rcases hsym with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  exact hn z hX hm lam hl hnonneg hj

end DefocusingNLS

end OAI
