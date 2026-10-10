import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugePair
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeODEUniqueness

namespace OAI

/-! Classical endpoint extensions agree with the interior physical gauge equation. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalGaugePair_eq_flux (Q : ℝ → ℂ) (U : ℝ → E₄) (r : ℝ)
    (hU : DifferentiableAt ℝ U r) :
    spectralPhysicalGaugePair Q (fun t => (U t).1.1) (fun t => (U t).1.2) r=
      (spectralFluxGaugeJet Q 1 U r,spectralFluxGaugeJet (fun t => star (Q t)) (-1) U r) := by
  have hf : DifferentiableAt ℝ (fun t => (U t).1.1) r := hU.fst.fst
  have hg : DifferentiableAt ℝ (fun t => (U t).1.2) r := hU.fst.snd
  have hpfun : spectralFluxCircularValue 1 U=
      (fun t => (U t).1.1)+(fun t => Complex.I*(U t).1.2) := by
    funext t
    simp [spectralFluxCircularValue]
  have hmfun : spectralFluxCircularValue (-1) U=
      (fun t => (U t).1.1)+(fun t => -Complex.I*(U t).1.2) := by
    funext t
    simp [spectralFluxCircularValue]
  have hp : deriv (spectralFluxCircularValue 1 U) r=
      deriv (fun t => (U t).1.1) r+Complex.I*deriv (fun t => (U t).1.2) r := by
    rw [hpfun]
    exact (hf.hasDerivAt.add (hg.hasDerivAt.const_mul Complex.I)).deriv
  have hm : deriv (spectralFluxCircularValue (-1) U) r=
      deriv (fun t => (U t).1.1) r-Complex.I*deriv (fun t => (U t).1.2) r := by
    rw [hmfun]
    simpa only [neg_mul,sub_eq_add_neg] using
      (hf.hasDerivAt.add (hg.hasDerivAt.const_mul (-Complex.I))).deriv
  simp only [spectralPhysicalGaugePair,spectralFluxGaugeJet,hp,hm,deriv.star,
    spectralFluxCircularValue,one_mul,neg_mul,sub_eq_add_neg]

theorem spectralPhysicalGaugePair_congr (Q f g F G : ℝ → ℂ) (r : ℝ)
    (hf : f =ᶠ[nhds r] F) (hg : g =ᶠ[nhds r] G) :
    spectralPhysicalGaugePair Q f g r=spectralPhysicalGaugePair Q F G r := by
  simp only [spectralPhysicalGaugePair,hf.eq_of_nhds,hg.eq_of_nhds,hf.deriv_eq,hg.deriv_eq]

theorem radialMatchedFreeGaugeExtension_hasDerivAt (ell : ℕ) (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R δ : ℝ)
    (hδ : radialShootingR (profileMatchingParameter z) ≤ δ) (ζ : ℂ) (U : ℝ → E₄)
    (hU : ∀ r ∈ Ioo (radialShootingR (profileMatchingParameter z)) R,
      HasDerivAt U (spectralFluxField ell (radialMatchedFreeMassFunction z r)
        (radialMatchedFreeTransportFunction z r) 6 ζ r (U r)) r)
    (f g : ℝ → ℂ) (hf : EqOn f (fun t => (U t).1.1) (Ioo δ R))
    (hg : EqOn g (fun t => (U t).1.2) (Ioo δ R)) (r : ℝ) (hr : r ∈ Ioo δ R) :
    HasDerivAt (spectralPhysicalGaugePair (radialShootingFreeExterior z) f g)
      (spectralFreePhysicalPairField (radialShootingB (profileMatchingParameter z)) ζ
        ((ell : ℂ)*((ell : ℂ)+10)) r
        (spectralPhysicalGaugePair (radialShootingFreeExterior z) f g r)) r := by
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
  have hd := ((radialMatchedFreeFlux_gauge_positive ell z hz₁ hz hc R ζ U hU r (hmem r hr)).prodMk
    (radialMatchedFreeFlux_gauge_negative ell z hz₁ hz hc R ζ U hU r (hmem r hr))).congr_of_eventuallyEq he
  exact hd.congr_deriv (congrArg
    (spectralFreePhysicalPairField (radialShootingB (profileMatchingParameter z)) ζ
      ((ell : ℂ)*((ell : ℂ)+10)) r) he.eq_of_nhds).symm

end DefocusingNLS

end OAI
