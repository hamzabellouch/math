import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxSystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeightedCircularEquation

namespace OAI

/-! Both circular weighted fluxes are consequences of the actual four-coordinate ODE. -/

open Set Filter
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralFluxCircularValue (σ : ℂ) (U : ℝ → E₄) (r : ℝ) : ℂ :=
  (U r).1.1+σ*Complex.I*(U r).1.2

noncomputable def spectralFluxCircularCurrent (σ : ℂ) (U : ℝ → E₄) (r : ℝ) : ℂ :=
  (U r).2.1+σ*Complex.I*(U r).2.2

theorem spectralFluxCircularValue_hasDerivAt (ell : ℕ) (σ ζ : ℂ)
    (μ A : ℝ → ℝ) (U : ℝ → E₄) (r : ℝ)
    (hU : HasDerivAt U (spectralFluxField ell (μ r) (A r) 6 ζ r (U r)) r) :
    HasDerivAt (spectralFluxCircularValue σ U)
      (((U r).2.1/(r : ℂ)^11+(A r : ℂ)*(U r).1.2)/(μ r : ℂ)+
        σ*Complex.I*(((U r).2.2/(r : ℂ)^11-(A r : ℂ)*(U r).1.1)/(μ r : ℂ))) r := by
  have hf : HasDerivAt (fun t => (U t).1.1)
      (spectralFluxField ell (μ r) (A r) 6 ζ r (U r)).1.1 r := hU.fst.fst
  have hg : HasDerivAt (fun t => (U t).1.2)
      (spectralFluxField ell (μ r) (A r) 6 ζ r (U r)).1.2 r := hU.fst.snd
  exact hf.add (hg.const_mul (σ*Complex.I))

theorem spectralFluxCircular_weighted_eq (ell : ℕ) (σ ζ : ℂ) (hσ : σ^2=1)
    (μ A : ℝ → ℝ) (U : ℝ → E₄) (r : ℝ) (hr : r ≠ 0) (hμ : μ r ≠ 0)
    (hU : HasDerivAt U (spectralFluxField ell (μ r) (A r) 6 ζ r (U r)) r) :
    spectralWeightedCircularFlux σ μ A (spectralFluxCircularValue σ U) r=
      spectralFluxCircularCurrent σ U r := by
  rw [spectralWeightedCircularFlux,(spectralFluxCircularValue_hasDerivAt ell σ ζ μ A U r hU).deriv]
  dsimp only [spectralFluxCircularValue,spectralFluxCircularCurrent]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hmC : (μ r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ
  field_simp [hrC,hmC]
  ring_nf
  simp only [hσ,Complex.I_sq]
  ring

theorem spectralFluxCircularCurrent_hasDerivAt (ell : ℕ) (σ ζ : ℂ) (hσ : σ^2=1)
    (μ A : ℝ → ℝ) (U : ℝ → E₄) (r : ℝ)
    (hU : HasDerivAt U (spectralFluxField ell (μ r) (A r) 6 ζ r (U r)) r) :
    HasDerivAt (spectralFluxCircularCurrent σ U)
      ((ell : ℂ)*((ell : ℂ)+10)*(r : ℂ)^9*(μ r : ℂ)*spectralFluxCircularValue σ U r+
        σ*Complex.I*(6-ζ)*(r : ℂ)^11*(μ r : ℂ)*spectralFluxCircularValue σ U r) r := by
  have hf : HasDerivAt (fun t => (U t).2.1)
      (spectralFluxField ell (μ r) (A r) 6 ζ r (U r)).2.1 r := hU.snd.fst
  have hg : HasDerivAt (fun t => (U t).2.2)
      (spectralFluxField ell (μ r) (A r) 6 ζ r (U r)).2.2 r := hU.snd.snd
  have hd : HasDerivAt (spectralFluxCircularCurrent σ U)
      (((spectralFluxField ell (μ r) (A r) 6 ζ r (U r)).2.1)+
        σ*Complex.I*((spectralFluxField ell (μ r) (A r) 6 ζ r (U r)).2.2)) r :=
    hf.add (hg.const_mul (σ*Complex.I))
  apply hd.congr_deriv
  dsimp only [spectralFluxField,spectralFluxCircularValue]
  ring_nf
  simp only [hσ,Complex.I_sq]
  ring

theorem spectralFluxCircular_hasDerivAt (ell : ℕ) (σ ζ : ℂ) (hσ : σ^2=1)
    (μ A : ℝ → ℝ) (U : ℝ → E₄) (l R : ℝ) (hl : 0 < l)
    (hμ : ∀ r ∈ Ioo l R, μ r ≠ 0)
    (hU : ∀ r ∈ Ioo l R,
      HasDerivAt U (spectralFluxField ell (μ r) (A r) 6 ζ r (U r)) r)
    (r : ℝ) (hr : r ∈ Ioo l R) :
    HasDerivAt (spectralWeightedCircularFlux σ μ A (spectralFluxCircularValue σ U))
      ((ell : ℂ)*((ell : ℂ)+10)*(r : ℂ)^9*(μ r : ℂ)*spectralFluxCircularValue σ U r+
        σ*Complex.I*(6-ζ)*(r : ℂ)^11*(μ r : ℂ)*spectralFluxCircularValue σ U r) r := by
  have he : spectralWeightedCircularFlux σ μ A (spectralFluxCircularValue σ U) =ᶠ[nhds r]
      spectralFluxCircularCurrent σ U := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact spectralFluxCircular_weighted_eq ell σ ζ hσ μ A U t (hl.trans ht.1).ne'
      (hμ t ht) (hU t ht)
  exact (spectralFluxCircularCurrent_hasDerivAt ell σ ζ hσ μ A U r (hU r hr)).congr_of_eventuallyEq he

end DefocusingNLS

end OAI
