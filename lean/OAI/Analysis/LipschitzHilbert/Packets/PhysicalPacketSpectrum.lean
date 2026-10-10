import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketSpectrum
import OAI.Analysis.LipschitzHilbert.Fourier.PhysicalPlanarJet

namespace OAI

/-! The original physical packet spectrum supplies Fourier cutoffs for
the actual three raw kernels on every affine reference line. The exact
dyadic endpoint identity puts these cutoffs in the form required by
the scaled annular-variation estimate. -/

noncomputable section

open scoped FourierTransform

namespace LipschitzHilbert

section PhysicalPacket

variable (f : SchwartzMap (ℝ × ℝ) ℂ)
  (a b ell W θ frequency scale c s w cStar cEta CEta cb Cb : ℝ)
  (hell : 0 < ell) (hW : 0 < W) (hw : 0 < w) (hcEta : 0 < cEta)
  (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
  (hspectrum : ∀ ξ η,
    planarAngularFourier (physicalPlanarPacket f a b ell W θ frequency hell.ne' hW.ne')
      (ξ, η) ≠ 0 →
    |ξ + θ * η| ≤ cStar / ell ∧ cEta ≤ w * η ∧ w * η ≤ CEta)
  (hselector : cb * w / ell ≤ |s - θ| ∧ |s - θ| ≤ Cb * w / ell)

include hell hW hw hcEta hcb hCb hspectrum hselector in
/-- No Fourier assumption on the derived raw kernels is needed: their
low and high cutoffs follow from the original physical packet. -/
theorem physicalPlanarJet_fourier_cutoffs (i : Fin 3) :
    (∀ ξ, |ξ| < (cEta * cb - cStar) / (2 * Real.pi * ell) →
      𝓕 (modulatedPlanarJet f a (b - s * a) ell W (s - θ)
        frequency scale c hell.ne' i) ξ = 0) ∧
    (∀ ξ, (CEta * Cb + cStar) / (2 * Real.pi * ell) < |ξ| →
      𝓕 (modulatedPlanarJet f a (b - s * a) ell W (s - θ)
        frequency scale c hell.ne' i) ξ = 0) := by
  have h := sourcePacket_jet_fourier_cutoffs
    (physicalPlanarPacket f a b ell W θ frequency hell.ne' hW.ne')
    c s θ ell w cStar cEta CEta cb Cb hell hw hcEta hcb hCb
    hspectrum hselector frequency scale i
  simpa only [physicalPlanarPacket_jet_slice] using h

end PhysicalPacket

/-- Exact rescaling of either annulus endpoint for a dyadic physical
length. The same reference length `R` works for every index. -/
theorem packet_annulus_dyadic_scale (numerator R : ℝ) (j : ℕ) (hR : R ≠ 0) :
    numerator / (2 * Real.pi * (R / (2 : ℝ) ^ j)) =
      (numerator / (2 * Real.pi * R)) * (2 : ℝ) ^ j := by
  have hj : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
  field_simp [Real.pi_ne_zero, hR, hj]

section DyadicPacket

variable (f : SchwartzMap (ℝ × ℝ) ℂ)
  (a b ell W θ frequency scale c s w cStar cEta CEta cb Cb : ℝ)
  (hell : 0 < ell) (hW : 0 < W) (hw : 0 < w) (hcEta : 0 < cEta)
  (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
  (hspectrum : ∀ ξ η,
    planarAngularFourier (physicalPlanarPacket f a b ell W θ frequency hell.ne' hW.ne')
      (ξ, η) ≠ 0 →
    |ξ + θ * η| ≤ cStar / ell ∧ cEta ≤ w * η ∧ w * η ≤ CEta)
  (hselector : cb * w / ell ≤ |s - θ| ∧ |s - θ| ≤ Cb * w / ell)

include hell hW hw hcEta hcb hCb hspectrum hselector in
/-- The concrete raw kernels have the dyadic cutoffs used in scalar
and Hilbert annular variation, uniformly over all three covariant jets. -/
theorem physicalPlanarJet_dyadic_fourier_cutoffs
    (R : ℝ) (hR : 0 < R) (j : ℕ) (hlength : ell = R / (2 : ℝ) ^ j) (i : Fin 3) :
    (∀ ξ, |ξ| < ((cEta * cb - cStar) / (2 * Real.pi * R)) * (2 : ℝ) ^ j →
      𝓕 (modulatedPlanarJet f a (b - s * a) ell W (s - θ)
        frequency scale c hell.ne' i) ξ = 0) ∧
    (∀ ξ, ((CEta * Cb + cStar) / (2 * Real.pi * R)) * (2 : ℝ) ^ j < |ξ| →
      𝓕 (modulatedPlanarJet f a (b - s * a) ell W (s - θ)
        frequency scale c hell.ne' i) ξ = 0) := by
  have hl : (cEta * cb - cStar) / (2 * Real.pi * ell) =
      ((cEta * cb - cStar) / (2 * Real.pi * R)) * (2 : ℝ) ^ j := by
    rw [hlength, packet_annulus_dyadic_scale _ R j hR.ne']
  have hu : (CEta * Cb + cStar) / (2 * Real.pi * ell) =
      ((CEta * Cb + cStar) / (2 * Real.pi * R)) * (2 : ℝ) ^ j := by
    rw [hlength, packet_annulus_dyadic_scale _ R j hR.ne']
  simpa only [hl, hu] using physicalPlanarJet_fourier_cutoffs
    f a b ell W θ frequency scale c s w cStar cEta CEta cb Cb
    hell hW hw hcEta hcb hCb hspectrum hselector i

end DyadicPacket

end LipschitzHilbert

end

end OAI
