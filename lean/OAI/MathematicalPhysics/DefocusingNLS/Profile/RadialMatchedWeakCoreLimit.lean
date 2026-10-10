import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakCore
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakExterior
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeCoreLimit

namespace OAI

/-! The actual weak core imposes the free matching boundary form. -/

open Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedWeak_physical_core (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (u : SpectralHarmonicPair ell R)
    (hu : u ∈ spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)))
    (he : let hR := (radialMatchedCore_radius_pos z).trans hLR
      ∀ v : spectralHarmonicCoreSubspace ell R (radialShootingR (profileMatchingParameter z)),
        spectralHarmonicPairComplexForm ell R w u v=
          inner ℂ (radialMatchedLimitWeakOperator ell z hc R hR ζ B
            (spectralHarmonicObservation ell R hR u)) v)
    (X : ℝ → E₄)
    (hX : ContinuousOn X (Ico (radialShootingR (profileMatchingParameter z)) R))
    (hXe : let hR := (radialMatchedCore_radius_pos z).trans hLR
      EqOn X (spectralPhysicalGaugePair (radialShootingFreeExterior z)
        (spectralHarmonicRepresentative ell R hR u.fst)
        (spectralHarmonicRepresentative ell R hR u.snd))
        (Ioo (radialShootingR (profileMatchingParameter z)) R)) :
    spectralFreeCoreBoundary ell (radialShootingR (profileMatchingParameter z))
      (X (radialShootingR (profileMatchingParameter z)))=0 := by
  let L := radialShootingR (profileMatchingParameter z)
  have hL : 0 < L := radialMatchedCore_radius_pos z
  let hR := hL.trans hLR
  let Q := radialShootingFreeExterior z
  let f := spectralHarmonicRepresentative ell R hR u.fst
  let g := spectralHarmonicRepresentative ell R hR u.snd
  obtain ⟨hf,hdg,C,hC,hg⟩ := radialMatchedWeak_core ell z hc R hLR w hw ζ B u hu he
  have hsub : Ico L R ⊆ Ioo 0 R := fun r hr => ⟨hL.trans_le hr.1,hr.2⟩
  have hQc : ContinuousOn Q (Ico L R) := fun r hr =>
    (radialShootingFreeExterior_hasDerivAt z r (hL.trans_le hr.1)).continuousAt.continuousWithinAt
  have hDQ : ContinuousOn (deriv Q) (Ico L R) := fun r hr =>
    (radialShootingFreeExterior_hasDerivAt_deriv z r (hL.trans_le hr.1)).continuousAt.continuousWithinAt
  apply spectralPhysicalGaugePair_core_of_open_eq ell L R hLR Q f g X hQc hDQ
    ((spectralHarmonicRepresentative_continuousOn ell R hR u.fst).mono hsub)
    ((spectralHarmonicRepresentative_continuousOn ell R hR u.snd).mono hsub)
    (hdg.mono hsub) hX hXe
  · exact radialShootingFreeExterior_core_value z hz₁ hz
  · exact radialShootingFreeExterior_neumann z hz
  · exact hf L ⟨hL,le_rfl⟩
  · simpa only [div_mul_eq_mul_div] using hg

end DefocusingNLS

end OAI
