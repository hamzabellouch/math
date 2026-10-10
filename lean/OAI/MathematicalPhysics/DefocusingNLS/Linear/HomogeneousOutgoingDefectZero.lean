import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingComparison

namespace OAI

/-! # Radial square integrability forces the outgoing defect to vanish

A nonzero defect has a fixed polynomial energy lower bound. The exact
high-derivative comparison and the twelve-dimensional radial measure
contradict that bound, even with the decaying outgoing remainder present.
-/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

local notation "V" => ℂ × ℂ

theorem homogeneousOutgoingDefect_eq_zero
    (W e : ℝ → V) (omega₁ omega₂ : ℝ → ℝ) (f g : ℝ → ℂ)
    (R d M beta C B : ℝ) (N : ℕ)
    (hR : 0 < R) (hM : 0 ≤ M) (hC : 0 < C)
    (hbeta : -6 ≤ beta - d) (hgap : 0 < (N : ℝ) + beta - d)
    (hW : ∀ r, R ≤ r → HasDerivAt W
      (-(((d / r : ℝ) : ℂ) + Complex.I * omega₁ r) * (W r).1 - (e r).1,
        -(((d / r : ℝ) : ℂ) + Complex.I * omega₂ r) * (W r).2 - (e r).2) r)
    (he : ∀ r, R ≤ r → ‖e r‖ ≤ M / r ^ 3 * ‖W r‖)
    (hcomparison : ∀ᶠ r in atTop, r ^ (2 * beta) * homogeneousPairEnergy (W r) ≤
      C * homogeneousPairEnergy (f r, g r) + B * r ^ (-2 * (N : ℝ)))
    (hf : IntegrableOn (fun r => r ^ (11 : ℕ) * ‖f r‖ ^ 2) (Ioi R))
    (hg : IntegrableOn (fun r => r ^ (11 : ℕ) * ‖g r‖ ^ 2) (Ioi R)) :
    ∀ r, R ≤ r → W r = 0 := by
  intro r hr
  by_contra hn
  obtain ⟨c, hc, hlower⟩ := homogeneousDefect_nonzero_power_bound W e
    omega₁ omega₂ d M r hM (hR.trans_le hr) hn
    (fun s hs => hW s (hr.trans hs)) (fun s hs => he s (hr.trans hs))
  have hlower' : ∀ᶠ s in atTop, c ≤ s ^ (2 * d) * homogeneousPairEnergy (W s) :=
    (eventually_ge_atTop r).mono hlower
  exact radial_pair_not_integrable_of_defect_remainder f g
    (fun s => homogeneousPairEnergy (W s)) R beta d c C B N hc hC
      hbeta hgap hlower' hcomparison ⟨hf, hg⟩

end DefocusingNLS

end OAI
