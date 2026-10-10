import OAI.MathematicalPhysics.Boltzmann.Branching.CumulativeIntervalBalance

namespace OAI

/-! # Reconstructing a time balance from finite gain and loss measures -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem ae_cumulative_balance {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : LocallyIntegrable f) (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ t, deriv ψ t*f t)+(∫ t, ψ t ∂μ)-(∫ t, ψ t ∂ν) = 0) :
    ∃ c : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b → f t = c+cumulative μ t-cumulative ν t := by
  let g : ℝ → ℝ := fun t => f t-cumulative μ t+cumulative ν t
  have hg : LocallyIntegrable g :=
    (hf.sub (cumulative_locallyIntegrable μ)).add (cumulative_locallyIntegrable ν)
  have hgw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ t, deriv ψ t*g t) = 0 := by
    intro ψ hψ hc hs
    have hd := hψ.continuous_deriv (by simp)
    have hfi : Integrable (fun t => deriv ψ t*f t) :=
      hf.integrable_smul_left_of_hasCompactSupport hd hc.deriv
    have hμi : Integrable (fun t => deriv ψ t*cumulative μ t) :=
      (cumulative_locallyIntegrable μ).integrable_smul_left_of_hasCompactSupport hd hc.deriv
    have hνi : Integrable (fun t => deriv ψ t*cumulative ν t) :=
      (cumulative_locallyIntegrable ν).integrable_smul_left_of_hasCompactSupport hd hc.deriv
    have hisub : Integrable (fun t => deriv ψ t*f t-deriv ψ t*cumulative μ t) := hfi.sub hμi
    have he : (∫ t, deriv ψ t*g t) =
        (∫ t, deriv ψ t*f t)-(∫ t, deriv ψ t*cumulative μ t)+
          (∫ t, deriv ψ t*cumulative ν t) := by
      calc
        _ = ∫ t, (deriv ψ t*f t-deriv ψ t*cumulative μ t)+deriv ψ t*cumulative ν t := by
          apply integral_congr_ae
          exact ae_of_all _ (fun t => by dsimp only [g]; ring)
        _ = _ := by rw [integral_add hisub hνi,integral_sub hfi hμi]
    rw [he,cumulative_weak_derivative μ hψ hc,cumulative_weak_derivative ν hψ hc]
    linarith [hw ψ hψ hc hs]
  obtain ⟨c,hc⟩ := ae_eq_const_of_weak_deriv_zero hab hg hgw
  refine ⟨c,hc.mono (fun t ht hmem => ?_)⟩
  have h := ht hmem
  dsimp only [g] at h
  linarith

end BoltzmannNonuniqueness.WeakTime

end

end OAI
