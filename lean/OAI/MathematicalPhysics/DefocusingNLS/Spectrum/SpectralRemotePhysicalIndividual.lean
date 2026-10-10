import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalReduction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteReductionRestriction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIndividualOperations

namespace OAI

/-! Individual outgoing symbols pass through both actual changes of frame.
These estimates are used only for qualitative cancellation at infinity. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_initial_individual
    (c : ℕ → ℝ → Fin 2 → ℝ) (B : ℕ → ℝ → SpectralRemoteOperator) (n : ℕ)
    (hc : HasLogJetBound 0 (c n)) (hB : HasLogJetBound 0 (B n))
    (hsmall : ∀ᶠ t in atTop, ∀ k, |c n t k| ≤ 1/32) :
    HasLogJetBound 0 (fun t => spectralRemoteInitialFrame (c n t)) ∧
      HasLogJetBound 0 (fun t => Ring.inverse (spectralRemoteInitialFrame (c n t))) ∧
      HasLogJetBound 0 (spectralRemoteInitialRemainder c B n) := by
  have hL : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨S,hS⟩ := eventually_atTop.mp hsmall
  have hs : ∀ᶠ j : ℕ in atTop, ∀ t ∈ Ioi (j : ℝ), ∀ k, |c n t k| ≤ 1/32 := by
    filter_upwards [hL.eventually (eventually_ge_atTop S)] with j hj
    intro t ht
    exact hS t (hj.trans ht.le)
  have hf := spectralRemote_initial_frame_symbols (HasUniformLogJetBound.of_single hc hL) hs
  have hp := hf.1.to_single
  have hi := hf.2.to_single
  refine ⟨hp,hi,?_⟩
  have hprod : HasLogJetBound 0 (fun t => B n t*spectralRemoteInitialFrame (c n t)) := by
    simpa only [zero_add] using hB.mul hp
  have hh := hi.mul (hprod.sub hp.deriv)
  convert hh using 1
  · norm_num
  · rfl

theorem spectralRemote_physical_reduced_individual
    (c : ℕ → ℝ → Fin 2 → ℝ) (B : ℕ → ℝ → SpectralRemoteOperator)
    (Y : ℕ → ℝ → SpectralRemoteSpace) (m n : ℕ) (sigma : ℝ)
    (hc : HasLogJetBound 0 (c n)) (hB : HasLogJetBound 0 (B n))
    (hY : HasLogJetBound sigma (Y n))
    (hsmall : ∀ᶠ t in atTop, ∀ k, |c n t k| ≤ 1/32) :
    HasLogJetBound sigma (spectralRemotePhysicalReducedSolution c B Y m n) := by
  obtain ⟨_,hi,hB'⟩ := spectralRemote_initial_individual c B n hc hB hsmall
  have hd := spectralRemote_root_reduction_single c (spectralRemoteInitialRemainder c B) m n hc hB' hsmall
  let restrict := ContinuousLinearMap.restrictScalarsL ℂ SpectralRemoteSpace SpectralRemoteSpace ℝ ℝ
  have hh := (hd.2.2.2.map restrict).apply ((hi.map restrict).apply hY)
  convert hh using 1
  · ring
  · rfl

end DefocusingNLS

end OAI
