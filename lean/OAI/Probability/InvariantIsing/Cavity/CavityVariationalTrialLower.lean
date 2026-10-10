import OAI.Probability.InvariantIsing.Cavity.CavityEntropyMaximum

namespace OAI

/-! Passing from the convergent physical entropy trial to the finite
spectral variational lower bound. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_variational_lower_of_trial_limit {m : ℕ}
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0<ρ a) (hsum : ∑ a, ρ a=1)
    (p : OverlapPath) (f A : ℕ → ℝ) (hent : entropyFunctional p ≠ ⊤)
    (hconv : Tendsto f atTop
      (𝓝 ((entropyFunctional p).toReal+spectralFunctional (finiteR ρ lam hρ hsum) p)))
    (hlower : ∀ ε>0, ∀ᶠ r in atTop, f r-A r<ε) :
    ∀ ε>0, ∀ᶠ r in atTop,
      (variationalFunctional (finiteR ρ lam hρ hsum)).toReal-A r<ε := by
  have hbot : entropyFunctional p ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (entropyFunctional_nonneg p)
  have hfinite := finiteVariational_ne_top_bot ρ lam hρ hsum
  have hi := iInf_le (fun q : OverlapPath => entropyFunctional q+
    (spectralFunctional (finiteR ρ lam hρ hsum) q : EReal)) p
  change variationalFunctional (finiteR ρ lam hρ hsum) ≤ _ at hi
  rw [← EReal.coe_toReal hfinite.1 hfinite.2, ← EReal.coe_toReal hent hbot,
    ← EReal.coe_add] at hi
  have hi' : (variationalFunctional (finiteR ρ lam hρ hsum)).toReal ≤
      (entropyFunctional p).toReal+spectralFunctional (finiteR ρ lam hρ hsum) p := by
    exact_mod_cast hi
  intro ε hε
  have he : 0<ε/2 := by positivity
  have hc := hconv.eventually (lt_mem_nhds (show
    (entropyFunctional p).toReal+spectralFunctional (finiteR ρ lam hρ hsum) p-ε/2 <
    (entropyFunctional p).toReal+spectralFunctional (finiteR ρ lam hρ hsum) p by linarith))
  filter_upwards [hc, hlower (ε/2) he] with r hr hl
  linarith

end InvariantIsing

end

end OAI
