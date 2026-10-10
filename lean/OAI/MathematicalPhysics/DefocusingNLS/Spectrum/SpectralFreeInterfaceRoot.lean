import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeRobinPropagation

namespace OAI

/-! A nonzero free solution with the actual core and outgoing conditions is a certified determinant zero. -/

open Set
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFreeRobin_core_nonzero_root (ell : ℕ) (b : ℝ) (ζ : ℂ)
    (hζ : -(1/32 : ℝ) ≤ ζ.re) (X : ℝ → E₄) (L R : ℝ) (hL : 0 < L) (hLR : L < R)
    (hX : ContinuousOn X (Icc L R))
    (hD : ∀ r ∈ Ioo L R,
      HasDerivAt X (spectralFreePhysicalPairField b ζ ((ell : ℂ)*((ell : ℂ)+10)) r (X r)) r)
    (hdet : spectralValueDet (spectralPhysicalValueMap (spectralFreePositivePhysical ell b ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell b ζ R)) ≠ 0)
    (hB : spectralPhysicalDerivativeMap (X R)=
      spectralJetRobin (spectralFreePositivePhysical ell b ζ R)
        (spectralFreeNegativePhysical ell b ζ R) (spectralPhysicalValueMap (X R)))
    (hcore : spectralFreeCoreBoundary ell L (X L)=0)
    (hne : ∃ r ∈ Icc L R, X r ≠ 0) :
    spectralSlowDeterminant ell b (L^2/4) ζ=0 := by
  by_contra hroot
  have hd : matchingColumnDeterminant
      (spectralFreeCoreBoundary ell L (spectralFreePositivePhysical ell b ζ L))
      (spectralFreeCoreBoundary ell L (spectralFreeNegativePhysical ell b ζ L)) ≠ 0 := by
    rw [spectralFreeNegativePhysical_eq]
    exact fun h => hroot ((spectralFreeCoreBoundary_zero_iff_spectralSlowDeterminant ell b L ζ hL hζ).mp h)
  obtain ⟨c,hc⟩ := spectralFreeRobin_propagation ell b ζ hζ X L R hL hLR hX hD hdet hB
  rw [hc ⟨le_rfl,hLR.le⟩,spectralFreeCoreBoundary_linear] at hcore
  obtain ⟨hc1,hc2⟩ := matchingColumn_coefficients_zero _ _ c.1 c.2 hd hcore
  obtain ⟨r,hr,hnr⟩ := hne
  apply hnr
  rw [hc hr]
  simp only [hc1,hc2,zero_smul,add_zero]

end DefocusingNLS

end OAI
