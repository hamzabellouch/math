import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ConditionalMain

namespace OAI

/-! # The Gaussian data do not almost surely admit global classical solutions -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

attribute [local irreducible] HasFiniteTimeSelfSimilarBlowup
  maximalSobolevInteractionDomain

theorem gaussian_not_almost_sure_global_conditional (hRou : RectangleRouche) (p₀ : ℕ) :
    ∃ p k : ℕ, p₀ ≤ p ∧ Odd p ∧ 3 ≤ p ∧ ∃ hk : 8 < (k : ℝ),
      ∀ α : ℝ, (k : ℝ) + 6 < α →
        ¬ ∀ᵐ f ∂weightedGaussianLaw k α,
          maximalSobolevInteractionDomain k (by linarith) ((p - 1) / 2) f = univ := by
  obtain ⟨p, k, hp, hodd, hp3, hk, U, _, _, hU, hGauss⟩ := gaussian_blowup_conditional hRou p₀
  refine ⟨p, k, hp, hodd, hp3, hk, ?_⟩
  intro α hα hglobal
  have hnot : ∀ᵐ f ∂weightedGaussianLaw k α, f ∉ U := by
    filter_upwards [hglobal] with f hf
    intro hfU
    have hblow := (hU f hfU).2
    unfold HasFiniteTimeSelfSimilarBlowup at hblow
    obtain ⟨T, _, x, c, _, _, hb, _⟩ := hblow
    rw [hf] at hb
    exact not_bddAbove_univ hb
  have hzero : weightedGaussianLaw k α U = 0 := by
    simpa only [not_not, ofPred_mem_eq] using (ae_iff.mp hnot)
  exact (hGauss α hα).2.2.ne' hzero

end DefocusingNLS

end OAI
