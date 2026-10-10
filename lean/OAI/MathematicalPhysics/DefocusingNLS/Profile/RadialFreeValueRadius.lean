import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreePhysicalIdentification
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeColumnNormalization

namespace OAI

/-! Choose a matching radius where the actual free H value matrix is invertible. -/

open Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialFreeValueDet_large_radius (ell : ℕ) (z : ProfileMatchingBall)
    (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re) :
    ∃ R : ℝ, innerBoundaryRadius < R ∧ radialShootingR (profileMatchingParameter z) < R ∧
      spectralValueDet
        (spectralPhysicalValueMap (spectralFreePositivePhysical ell
          (radialShootingB (profileMatchingParameter z)) lam R))
        (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
          (radialShootingB (profileMatchingParameter z)) lam R)) ≠ 0 := by
  let β := radialShootingB (profileMatchingParameter z)
  have hq (h : ℝ) : -1 < (spectralQ ell h β lam).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have hd := spectralPhysicalValueDet_eventually_ne_zero
    (2*Complex.I*(β : ℂ)-2*lam) (star (2*Complex.I*(β : ℂ))-2*lam)
    (spectralFreeFirstColumn ell (spectralQ ell 1 β lam))
    (spectralFreeSecondColumn ell (spectralQ ell (-1) β lam))
    (spectralFreeFirstColumn_tendsto ell _ (hq 1))
    (spectralFreeSecondColumn_tendsto ell _ (hq (-1)))
  obtain ⟨R,hR,hdR⟩ := ((eventually_gt_atTop
    (max innerBoundaryRadius (radialShootingR (profileMatchingParameter z)))).and hd).exists
  exact ⟨R,(le_max_left _ _).trans_lt hR,(le_max_right _ _).trans_lt hR,
    by simpa only [spectralFreePhysicalPair_first,spectralFreePhysicalPair_second] using hdR⟩

end DefocusingNLS

end OAI
