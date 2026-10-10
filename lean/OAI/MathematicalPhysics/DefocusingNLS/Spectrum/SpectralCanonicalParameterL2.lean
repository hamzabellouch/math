import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalParameterPower
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailWeightedL2

namespace OAI

/-! The differentiated canonical outgoing values have finite weighted top energy. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonicalPhysicalParameterValues_top_integrable (ν η b : ℂ) (n : ℕ) (hn : 1≤n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ)
    (σ : ℝ) (hσ : 0<σ) (N : ℕ)
    (hs : 11+2*(ν.re-2*z.re+σ-(N : ℝ)) < -1) :
    ∃ T : ℝ, 1<T ∧ IntegrableOn
      (fun r => r^11*‖iteratedDeriv N (canonicalPhysicalParameterValues ν Y z) r‖^2) (Ioi T) := by
  let f := fun t => (circularParameterShear t (Y z t) (deriv (fun lam => Y lam t) z)).1.1
  let g := fun t => (circularParameterShear t (Y z t) (deriv (fun lam => Y lam t) z)).2.1
  have hj := canonical_parameterShear_value_logJets ν η b n hn L hX hb c Y hY z σ hσ
  have hsame : (ν-2*z).re=(star ν-2*z).re := by simp
  have hs' : 11+2*((ν-2*z).re+σ-(N : ℝ)) < -1 := by
    simpa only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
      zero_mul,sub_zero] using hs
  obtain ⟨T,hT,hi⟩ := spectralPowerValues_top_integrable (ν-2*z) (star ν-2*z)
    hsame f g σ hj.1 hj.2 N hs'
  refine ⟨T,hT,hi.congr_fun ?_ measurableSet_Ioi⟩
  intro r hr
  have hr₁ : 1<r := hT.trans hr
  have heq : canonicalPhysicalParameterValues ν Y z =ᶠ[𝓝 r]
      spectralPowerValues (ν-2*z) (star ν-2*z) f g := by
    filter_upwards [Ioi_mem_nhds hr₁] with s hs
    exact canonicalPhysicalParameterValues_eq ν η b n L c Y hY z s hs
  dsimp only
  rw [heq.iteratedDeriv_eq N]

end DefocusingNLS

end OAI
