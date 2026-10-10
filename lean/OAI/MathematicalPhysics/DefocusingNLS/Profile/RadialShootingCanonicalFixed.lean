import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicFixedLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSubunitCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingComplexLimit

namespace OAI

/-! Fixed-interval convergence for the actual shooting-profile outgoing columns. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialShootingNu_parameter_tendsto
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun n => radialShootingNu n (z n)) atTop
      (𝓝 (2*Complex.I*(radialShootingB (profileMatchingParameter z₀) : ℂ))) := by
  have ht := radialShootingNu_subsequence_tendsto id strictMono_id z z₀ hz
  have he : -2*radialShootingQ z₀=
      2*Complex.I*(radialShootingB (profileMatchingParameter z₀) : ℂ) := by
    unfold radialShootingQ
    ring
  simpa only [Function.id_def,he] using ht

theorem radialShooting_canonical_fixed_limit
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀)) (ell : ℕ)
    (Y Z : ℕ → ℂ → ℝ → E₄)
    (hY : ∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (radialShootingNu n (z n))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z n)) n
      (Real.log innerBoundaryRadius) (1,0) (Y n))
    (hZ : ∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (radialShootingNu n (z n))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z n)) n
      (Real.log innerBoundaryRadius) (0,1) (Z n))
    (lam : ℕ → ℂ) (lam₀ : ℂ) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hlam₀ : -(1/32 : ℝ) ≤ lam₀.re)
    (A : ℝ) (hA : 0 ≤ A) (hLA : Real.log innerBoundaryRadius ≤ A) :
    TendstoUniformlyOn (fun n => Y n (lam n))
      (spectralFreeFirstColumn ell
        (spectralQ ell 1 (radialShootingB (profileMatchingParameter z₀)) lam₀)) atTop (Ici A) ∧
    TendstoUniformlyOn (fun n => Z n (lam n))
      (spectralFreeSecondColumn ell
        (spectralQ ell (-1) (radialShootingB (profileMatchingParameter z₀)) lam₀)) atTop (Ici A) := by
  let ν := fun n => radialShootingNu n (z n)
  let m := fun n => radialShootingM (z n)
  let b := radialShootingB (profileMatchingParameter z₀)
  have hν : Tendsto ν atTop (𝓝 (2*Complex.I*(b : ℂ))) :=
    radialShootingNu_parameter_tendsto z z₀ hz
  have hm : Tendsto m atTop (𝓝 (radialShootingM z₀)) :=
    continuous_radialShootingM.continuousAt.tendsto.comp hz
  have hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n)
      (Real.log innerBoundaryRadius) := by
    filter_upwards [radialShootingExterior_exists] with n hn
    exact hn (z n)
  obtain ⟨δ,ρ,hδ,_hδm,hsmall,_hρ,_hu,_hl⟩ := radialShooting_free_annulus z₀
  obtain ⟨ε,hε,hεlim,hc⟩ := radialShooting_spectralCoefficients_uniform_small
  apply canonical_holomorphic_H_fixed_limit ν m lam b (radialShootingM z₀) lam₀ ell
    hν hm hlam hlam₀ δ (Real.log innerBoundaryRadius) hδ hsmall hX Y Z hY hZ
    A hA ε hε hεlim
  filter_upwards [hc] with n hn t ht
  exact hn (z n) t (hLA.trans ht)

end DefocusingNLS

end OAI
