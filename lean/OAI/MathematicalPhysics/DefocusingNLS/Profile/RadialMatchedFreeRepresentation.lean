import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakPhysical
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakExterior

namespace OAI

/-! A limiting weak kernel belongs to the exact outgoing H-column span. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedWeak_free_representation_of_boundary (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re) (u : SpectralHarmonicPair ell R)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hBoundary : B=spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
      (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R)
        (spectralJetRobin
          (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
          (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))))
    (he : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u v=
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    ∃ c : ℂ × ℂ, EqOn
      (spectralPhysicalGaugePair (radialShootingFreeExterior z)
        (spectralHarmonicRepresentative ell R hR u.fst)
        (spectralHarmonicRepresentative ell R hR u.snd))
      (fun r => c.1 • spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ r+
        c.2 • spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ r)
      (Ioo (radialShootingR (profileMatchingParameter z)) R) := by
  dsimp only at he ⊢
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := radialMatchedCore_radius_pos z
  let hR := hL.trans hLR
  let δ := (L+R)/2
  have hlδ : L < δ := by dsimp [δ]; linarith
  have hδR : δ < R := by dsimp [δ]; linarith
  let b := radialShootingB (profileMatchingParameter z)
  let Q := radialShootingFreeExterior z
  let M := spectralJetRobin (spectralFreePositivePhysical ell b ζ R)
    (spectralFreeNegativePhysical ell b ζ R)
  let F := spectralHarmonicRepresentative ell R hR u.fst
  let G := spectralHarmonicRepresentative ell R hR u.snd
  let X := spectralPhysicalGaugePair Q F G
  obtain ⟨f,g,_,_,_,_,hef,heg,hX,hD,hB⟩ :=
    radialMatchedWeak_physical_extension_of_boundary ell z hz₁ hz hc R hLR δ hlδ hδR w hw ζ M B hBoundary u he
  obtain ⟨c,hcoeff⟩ := spectralFreeRobin_propagation ell b ζ hζ
    (spectralPhysicalGaugePair Q f g) δ R (hL.trans hlδ) hδR hX hD hdet hB
  have hec : EqOn X (fun r => c.1 • spectralFreePositivePhysical ell b ζ r+
      c.2 • spectralFreeNegativePhysical ell b ζ r) (Ioo δ R) := by
    intro r hr
    have hf : f =ᶠ[nhds r] F := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
      exact hef ⟨ht.1.le,ht.2.le⟩
    have hg : g =ᶠ[nhds r] G := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
      exact heg ⟨ht.1.le,ht.2.le⟩
    exact (spectralPhysicalGaugePair_congr Q f g F G r hf hg).symm.trans
      (hcoeff ⟨hr.1.le,hr.2.le⟩)
  have hDX := radialMatchedWeak_physical_hasDerivAt ell z hz₁ hz hc R hLR w hw ζ B u he
  have hDY : ∀ r ∈ Ioo L R, HasDerivAt
      (fun r => c.1 • spectralFreePositivePhysical ell b ζ r+
        c.2 • spectralFreeNegativePhysical ell b ζ r)
      (spectralFreePhysicalPairField b ζ ((ell : ℂ)*((ell : ℂ)+10)) r
        (c.1 • spectralFreePositivePhysical ell b ζ r+
          c.2 • spectralFreeNegativePhysical ell b ζ r)) r := by
    intro r hr
    exact spectralFreeCombination_hasDerivAt b ζ ((ell : ℂ)*((ell : ℂ)+10)) _ _ c.1 c.2 r
      (spectralFreePositivePhysical_hasDerivAt ell b ζ hζ r (hL.trans hr.1))
      (spectralFreeNegativePhysical_hasDerivAt ell b ζ hζ r (hL.trans hr.1))
  exact ⟨c,spectralFree_eq_on_open_of_collar b ζ ((ell : ℂ)*((ell : ℂ)+10)) X _
    L δ R hL hlδ hδR hDX hDY hec⟩

theorem radialMatchedWeak_free_representation (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (hζ : -(1/32 : ℝ) ≤ ζ.re) (u : SpectralHarmonicPair ell R)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)) ≠ 0)
    (he : let hR := (radialMatchedCore_radius_pos z).trans hLR
      let Q := radialShootingFreeExterior z
      let M := spectralJetRobin
        (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
        (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
      let B := spectralFluxBoundary R (radialMatchedFreeMassFunction z R)
        (radialMatchedFreeTransportFunction z R) (spectralGaugeRobin (Q R) (deriv Q R) M)
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u v=
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) v) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    ∃ c : ℂ × ℂ, EqOn
      (spectralPhysicalGaugePair (radialShootingFreeExterior z)
        (spectralHarmonicRepresentative ell R hR u.fst)
        (spectralHarmonicRepresentative ell R hR u.snd))
      (fun r => c.1 • spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ r+
        c.2 • spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ r)
      (Ioo (radialShootingR (profileMatchingParameter z)) R) := by
  apply radialMatchedWeak_free_representation_of_boundary ell z hz₁ hz hc R hLR w hw ζ hζ u hdet
    (spectralFluxBoundary R (radialMatchedFreeMassFunction z R) (radialMatchedFreeTransportFunction z R)
      (spectralGaugeRobin (radialShootingFreeExterior z R) (deriv (radialShootingFreeExterior z) R)
        (spectralJetRobin
          (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)
          (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) ζ R)))) rfl he

end DefocusingNLS

end OAI
