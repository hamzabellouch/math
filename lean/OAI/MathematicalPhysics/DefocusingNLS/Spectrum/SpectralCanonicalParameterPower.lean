import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailPowerBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalPhysicalParameter

namespace OAI

/-! Actual parameter derivatives of the outgoing values have the required radial powers. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def canonicalPhysicalParameterValues (ν : ℂ) (Y : ℂ → ℝ → E₄)
    (z : ℂ) (r : ℝ) : ℂ × ℂ :=
  spectralPhysicalValueMap
    (deriv (fun lam => spectralPhysicalPair (ν-2*lam) (star ν-2*lam) (Y lam) r) z)

theorem canonicalPhysicalParameterValues_eq (ν η b : ℂ) (n : ℕ) (L : ℝ)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ)
    (r : ℝ) (hr : 1<r) :
    canonicalPhysicalParameterValues ν Y z r =
      spectralPowerValues (ν-2*z) (star ν-2*z)
        (fun t => (circularParameterShear t (Y z t) (deriv (fun lam => Y lam t) z)).1.1)
        (fun t => (circularParameterShear t (Y z t) (deriv (fun lam => Y lam t) z)).2.1) r := by
  have hp := spectralPhysicalPair_hasParameterDerivAt ν (star ν) z Y
    (fun t => deriv (fun lam => Y lam t) z) r
    (hY.2.2.1 z (Real.log r) (Real.log_pos hr).le).differentiableAt.hasDerivAt
  rw [canonicalPhysicalParameterValues,hp.deriv]
  rfl

theorem canonicalPhysicalParameterValues_derivative_bound (ν η b : ℂ) (n : ℕ) (hn : 1≤n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ)
    (σ : ℝ) (hσ : 0<σ) (N : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ r in atTop,
      ‖iteratedDeriv N (canonicalPhysicalParameterValues ν Y z) r‖ ≤
        C*r^(ν.re-2*z.re+σ-(N : ℝ)) := by
  let f := fun t => (circularParameterShear t (Y z t) (deriv (fun lam => Y lam t) z)).1.1
  let g := fun t => (circularParameterShear t (Y z t) (deriv (fun lam => Y lam t) z)).2.1
  have hj := canonical_parameterShear_value_logJets ν η b n hn L hX hb c Y hY z σ hσ
  have hsame : (ν-2*z).re=(star ν-2*z).re := by simp
  obtain ⟨C,hC,hbd⟩ := spectralPowerValues_derivative_bound (ν-2*z) (star ν-2*z)
    hsame f g σ hj.1 hj.2 N
  refine ⟨C,hC,?_⟩
  filter_upwards [hbd,eventually_gt_atTop (1 : ℝ)] with r hr hr₁
  have heq : canonicalPhysicalParameterValues ν Y z =ᶠ[𝓝 r]
      spectralPowerValues (ν-2*z) (star ν-2*z) f g := by
    filter_upwards [Ioi_mem_nhds hr₁] with s hs
    exact canonicalPhysicalParameterValues_eq ν η b n L c Y hY z s hs
  rw [heq.iteratedDeriv_eq N]
  simpa only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,sub_zero] using hr

end DefocusingNLS

end OAI
