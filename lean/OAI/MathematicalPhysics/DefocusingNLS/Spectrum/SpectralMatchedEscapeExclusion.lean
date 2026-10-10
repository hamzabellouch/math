import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIConstructed
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchedCaseIIRatio
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace OAI

/-! The two constructed cases exclude every escaping angular/frequency
sequence of nonzero regular outgoing modes in the counting strip. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem spectralMatched_escape_exclusion
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i)=0)
    (N : ℕ) (hN : 7 ≤ N) (lam : ℕ → ℂ) (ell : ℕ → ℕ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (lam i).re) (hupper : ∀ i, (lam i).re ≤ 4)
    (hpos : ∀ i, 0 ≤ (lam i).im)
    (hescape : Tendsto (fun i => (ell i : ℝ)+(lam i).im) atTop atTop)
    (mode : ∀ i, RadialSpectralMode (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
      (radialMatchedProfile (s i) (z i)) (((ell i : ℝ)*(ell i+10) : ℝ) : ℂ) (lam i)) : False := by
  classical
  let ratio := fun i => ((ell i : ℝ)*(ell i+10))/(1+(lam i).im)
  by_cases hI : Tendsto ratio atTop atTop
  · exact spectralMatched_caseI s hs z z0 hz hX hmatch N hN lam ell hhalf hupper hpos hI
      (fun i => (mode i).first) (fun i => (mode i).second)
      (fun i => (mode i).first_c2) (fun i => (mode i).second_c2) (fun i => (mode i).equation)
      (fun i => (mode i).nonzero) (fun i => (mode i).bounded)
      (fun i => (mode i).first_top) (fun i => (mode i).second_top)
  · obtain ⟨C,hC⟩ : ∃ C : ℝ, ∃ᶠ i in atTop, ratio i < C := by
      simpa only [tendsto_atTop,not_forall,not_eventually,not_le] using hI
    obtain ⟨φ,hφ,hφC⟩ := exists_seq_forall_of_frequently hC
    obtain ⟨σ,_,hσ⟩ := strictMono_subseq_of_tendsto_atTop hφ
    let ψ := φ ∘ σ
    have hψ : StrictMono ψ := hσ
    have hbound i : ((ell (ψ i) : ℝ)*(ell (ψ i)+10))/(1+(lam (ψ i)).im) ≤ max C 0 :=
      (hφC (σ i)).le.trans (le_max_left _ _)
    have hw := spectral_bounded_ratio_frequency_growth (ell ∘ ψ) (fun i => (lam (ψ i)).im)
      (max C 0) (le_max_right _ _) (fun i => hpos (ψ i)) hbound (hescape.comp hψ.tendsto_atTop)
    exact spectralMatched_caseII_bounded_ratio (s ∘ ψ) (hs.comp hψ) (z ∘ ψ) z0
      (hz.comp hψ.tendsto_atTop) (fun i => hX (ψ i)) (fun i => hmatch (ψ i))
      N hN (lam ∘ ψ) (ell ∘ ψ) (fun i => hhalf (ψ i)) (fun i => hupper (ψ i)) hw
      (max C 0) (le_max_right _ _) hbound (fun i => mode (ψ i))

end DefocusingNLS

end OAI
