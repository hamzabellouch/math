import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFluxSystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxCircular

namespace OAI

/-! Both circular weighted fluxes are consequences of the actual four-coordinate ODE. -/

open Set Filter
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFluxChainCircularValue_hasDerivAt (ell : ℕ) (σ ζ : ℂ)
    (μ A : ℝ → ℝ) (U₀ U : ℝ → E₄) (r : ℝ)
    (hU : HasDerivAt U (spectralFluxField ell (μ r) (A r) 6 ζ r (U r) +
      spectralFluxFieldSlope (μ r) r (U₀ r)) r) :
    HasDerivAt (spectralFluxCircularValue σ U)
      (((U r).2.1/(r : ℂ)^11+(A r : ℂ)*(U r).1.2)/(μ r : ℂ)+
        σ*Complex.I*(((U r).2.2/(r : ℂ)^11-(A r : ℂ)*(U r).1.1)/(μ r : ℂ))) r := by
  have hf₀ : HasDerivAt (fun t => (U t).1.1)
      (spectralFluxField ell (μ r) (A r) 6 ζ r (U r) + spectralFluxFieldSlope (μ r) r (U₀ r)).1.1 r :=
    hU.fst.fst
  have hg₀ : HasDerivAt (fun t => (U t).1.2)
      (spectralFluxField ell (μ r) (A r) 6 ζ r (U r) + spectralFluxFieldSlope (μ r) r (U₀ r)).1.2 r :=
    hU.fst.snd
  have hf : HasDerivAt (fun t => (U t).1.1)
      (spectralFluxField ell (μ r) (A r) 6 ζ r (U r)).1.1 r := by
    simpa only [Prod.fst_add,spectralFluxFieldSlope,add_zero] using hf₀
  have hg : HasDerivAt (fun t => (U t).1.2)
      (spectralFluxField ell (μ r) (A r) 6 ζ r (U r)).1.2 r := by
    simpa only [Prod.fst_add,Prod.snd_add,spectralFluxFieldSlope,add_zero] using hg₀
  exact hf.add (hg.const_mul (σ*Complex.I))

theorem spectralFluxChainCircular_weighted_eq (ell : ℕ) (σ ζ : ℂ) (hσ : σ^2=1)
    (μ A : ℝ → ℝ) (U₀ U : ℝ → E₄) (r : ℝ) (hr : r ≠ 0) (hμ : μ r ≠ 0)
    (hU : HasDerivAt U (spectralFluxField ell (μ r) (A r) 6 ζ r (U r) +
      spectralFluxFieldSlope (μ r) r (U₀ r)) r) :
    spectralWeightedCircularFlux σ μ A (spectralFluxCircularValue σ U) r=
      spectralFluxCircularCurrent σ U r := by
  rw [spectralWeightedCircularFlux,(spectralFluxChainCircularValue_hasDerivAt ell σ ζ μ A U₀ U r hU).deriv]
  dsimp only [spectralFluxCircularValue,spectralFluxCircularCurrent]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hmC : (μ r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ
  field_simp [hrC,hmC]
  ring_nf
  simp only [hσ,Complex.I_sq]
  ring

theorem spectralFluxChainCircularCurrent_hasDerivAt (ell : ℕ) (σ ζ : ℂ) (hσ : σ^2=1)
    (μ A : ℝ → ℝ) (U₀ U : ℝ → E₄) (r : ℝ)
    (hU : HasDerivAt U (spectralFluxField ell (μ r) (A r) 6 ζ r (U r) +
      spectralFluxFieldSlope (μ r) r (U₀ r)) r) :
    HasDerivAt (spectralFluxCircularCurrent σ U)
      ((ell : ℂ)*((ell : ℂ)+10)*(r : ℂ)^9*(μ r : ℂ)*spectralFluxCircularValue σ U r+
        σ*Complex.I*(6-ζ)*(r : ℂ)^11*(μ r : ℂ)*spectralFluxCircularValue σ U r -
        σ*Complex.I*(r : ℂ)^11*(μ r : ℂ)*spectralFluxCircularValue σ U₀ r) r := by
  have hf : HasDerivAt (fun t => (U t).2.1)
      (spectralFluxField ell (μ r) (A r) 6 ζ r (U r) + spectralFluxFieldSlope (μ r) r (U₀ r)).2.1 r :=
    hU.snd.fst
  have hg : HasDerivAt (fun t => (U t).2.2)
      (spectralFluxField ell (μ r) (A r) 6 ζ r (U r) + spectralFluxFieldSlope (μ r) r (U₀ r)).2.2 r :=
    hU.snd.snd
  have hd := hf.add (hg.const_mul (σ*Complex.I))
  apply hd.congr_deriv
  dsimp only [spectralFluxField,spectralFluxFieldSlope,spectralFluxCircularValue,
    Prod.snd_add,Prod.fst_add]
  ring_nf
  simp only [hσ,Complex.I_sq]
  ring

theorem spectralFluxChainCircular_hasDerivAt (ell : ℕ) (σ ζ : ℂ) (hσ : σ^2=1)
    (μ A : ℝ → ℝ) (U₀ U : ℝ → E₄) (l R : ℝ) (hl : 0 < l)
    (hμ : ∀ r ∈ Ioo l R, μ r ≠ 0)
    (hU : ∀ r ∈ Ioo l R,
      HasDerivAt U (spectralFluxField ell (μ r) (A r) 6 ζ r (U r) +
      spectralFluxFieldSlope (μ r) r (U₀ r)) r)
    (r : ℝ) (hr : r ∈ Ioo l R) :
    HasDerivAt (spectralWeightedCircularFlux σ μ A (spectralFluxCircularValue σ U))
      ((ell : ℂ)*((ell : ℂ)+10)*(r : ℂ)^9*(μ r : ℂ)*spectralFluxCircularValue σ U r+
        σ*Complex.I*(6-ζ)*(r : ℂ)^11*(μ r : ℂ)*spectralFluxCircularValue σ U r -
        σ*Complex.I*(r : ℂ)^11*(μ r : ℂ)*spectralFluxCircularValue σ U₀ r) r := by
  have he : spectralWeightedCircularFlux σ μ A (spectralFluxCircularValue σ U) =ᶠ[nhds r]
      spectralFluxCircularCurrent σ U := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact spectralFluxChainCircular_weighted_eq ell σ ζ hσ μ A U₀ U t (hl.trans ht.1).ne'
      (hμ t ht) (hU t ht)
  exact (spectralFluxChainCircularCurrent_hasDerivAt ell σ ζ hσ μ A U₀ U r (hU r hr)).congr_of_eventuallyEq he

end DefocusingNLS

end OAI
