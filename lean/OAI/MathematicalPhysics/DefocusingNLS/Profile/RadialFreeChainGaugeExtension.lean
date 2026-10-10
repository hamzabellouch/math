import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeGaugeExtension
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeChainGauge
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeChainDifference

namespace OAI

/-! The forced flux equation transfers to the physical C1 extension. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedFreeGaugeExtension_chain_hasDerivAt (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R δ : ℝ)
    (hδ : radialShootingR (profileMatchingParameter z) ≤ δ) (ζ : ℂ) (U₀ U : ℝ → E₄)
    (hU₀ : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U₀ (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U₀ r)) r)
    (hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r)+spectralFluxFieldSlope (radialMatchedFreeMassFunction z r) r (U₀ r)) r)
    (f g : ℝ → ℂ) (hf : EqOn f (fun t => (U t).1.1) (Ioo δ R))
    (hg : EqOn g (fun t => (U t).1.2) (Ioo δ R)) (r : ℝ) (hr : r ∈ Ioo δ R) :
    HasDerivAt (spectralPhysicalGaugePair (radialShootingFreeExterior z) f g)
      (spectralFreePhysicalPairField (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r
        (spectralPhysicalGaugePair (radialShootingFreeExterior z) f g r) +
        spectralFreeChainSource (spectralPhysicalGaugePair (radialShootingFreeExterior z)
          (fun t => (U₀ t).1.1) (fun t => (U₀ t).1.2) r)) r := by
  have hmem (t : ℝ) (ht : t ∈ Ioo δ R) : t ∈ Ioo (radialShootingR (profileMatchingParameter z)) R :=
    ⟨hδ.trans_lt ht.1,ht.2⟩
  have he : spectralPhysicalGaugePair (radialShootingFreeExterior z) f g =ᶠ[nhds r]
      fun t => (spectralFluxGaugeJet (radialShootingFreeExterior z) 1 U t,
        spectralFluxGaugeJet (fun x => star (radialShootingFreeExterior z x)) (-1) U t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    have hft : f =ᶠ[nhds t] fun x => (U x).1.1 := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
      exact hf hx
    have hgt : g =ᶠ[nhds t] fun x => (U x).1.2 := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
      exact hg hx
    rw [spectralPhysicalGaugePair_congr _ _ _ _ _ t hft hgt]
    exact spectralPhysicalGaugePair_eq_flux _ U t (hU t (hmem t ht)).differentiableAt
  have hd := (radialMatchedFreeFluxChain_gauge_positive ell z hz₁ hz hc R ζ U₀ U hU₀ hU r (hmem r hr)).prodMk
    (radialMatchedFreeFluxChain_gauge_negative ell z hz₁ hz hc R ζ U₀ U hU₀ hU r (hmem r hr))
  have hzero := spectralPhysicalGaugePair_eq_flux (radialShootingFreeExterior z) U₀ r
    (hU₀ r (hmem r hr)).differentiableAt
  have heq := he.eq_of_nhds
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  rw [heq,hzero]
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralFreePhysicalPairField,spectralFreeChainSource,
      Prod.fst_add,Prod.snd_add,one_mul,neg_mul,neg_neg]

end DefocusingNLS

end OAI
