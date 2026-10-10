import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingFluxLimit

namespace OAI

/-! A uniformly vanishing local Robin error can be selected along one
subsequence, preserving all already established boundary limits. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralOutgoing_robin_limit (nu : ℕ → ℝ) (A D : ℝ) (hD : 0 ≤ D)
    (z w dz dw : ℕ → ℂ) (hnu : ∀ᶠ n in atTop, 0 ≤ nu n)
    (hz : Tendsto (fun n => nu n*‖z n‖) atTop (𝓝 0))
    (hdz : Tendsto dz atTop (𝓝 0))
    (hflux : Tendsto (fun n => nu n*(spectralScalarFlux (z n,dz n)+spectralScalarFlux (w n,dw n)))
      atTop (𝓝 0))
    (hrobin : ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop, ∃ alpha : ℂ,
      alpha.im ≤ -nu n/4 ∧ ‖alpha‖ ≤ A*nu n ∧
      ‖dw n-alpha*w n‖ ≤ delta*D*nu n*(‖z n‖+‖w n‖)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => nu (φ n)*‖w (φ n)‖) atTop (𝓝 0) ∧
      Tendsto (fun n => dw (φ n)) atTop (𝓝 0) := by
  classical
  let delta := fun n : ℕ => 1/((n : ℝ)+1)
  have hdelta n : 0 < delta n := by dsimp only [delta]; positivity
  have hdelta0 : Tendsto delta atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ,hφ,hall⟩ := extraction_forall_of_eventually (fun n => hnu.and (hrobin (delta n) (hdelta n)))
  choose alpha ha hb hc using fun n => (hall n).2
  have hh := spectralOutgoing_flux_limit (nu ∘ φ) (fun n => delta n*D) A
    (z ∘ φ) (w ∘ φ) (dz ∘ φ) (dw ∘ φ) alpha
    (by simpa only [zero_mul] using hdelta0.mul_const D)
    (hz.comp hφ.tendsto_atTop) (hdz.comp hφ.tendsto_atTop) (hflux.comp hφ.tendsto_atTop)
    (Eventually.of_forall (fun n => ⟨(hall n).1,mul_nonneg (hdelta n).le hD,ha n,hb n,hc n⟩))
  exact ⟨φ,hφ,hh.1,hh.2⟩

end DefocusingNLS

end OAI
