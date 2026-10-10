import OAI.Probability.InvariantIsing.Cavity.CavityTelescoping

namespace OAI

/-! A vanishing-error comparison transfers a cavity increment bound through
the scalar pressure envelope and back to the ordinary normalized pressure. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_envelope_progression_lower
    (A P Δ err : ℕ → ℝ) (N₀ step L : ℝ) (hN₀ : 0<N₀) (hstep : 0<step)
    (hclose : Tendsto (fun r => A r/(N₀+step*r)-P r) atTop (𝓝 0))
    (herr : Tendsto err atTop (𝓝 0))
    (hinc : ∀ r, Δ r-step*err r ≤ A (r+1)-A r)
    (hlower : ∀ ε>0, ∀ᶠ r in atTop, L-ε≤Δ r/step) :
    ∀ ε>0, ∀ᶠ r in atTop, L-ε≤P r := by
  have hA : ∀ ε>0, ∀ᶠ r in atTop, step*(L-ε)≤A (r+1)-A r := by
    intro ε hε
    have he := herr.eventually (eventually_lt_nhds (half_pos hε))
    filter_upwards [hlower (ε/2) (half_pos hε), he] with r hr he
    have hd := (le_div_iff₀ hstep).mp hr
    have hi := hinc r
    nlinarith
  have htel := cavity_progression_pressure_lower A N₀ step L hN₀ hstep hA
  intro ε hε
  have hc := hclose.eventually (eventually_lt_nhds (half_pos hε))
  filter_upwards [htel (ε/2) (half_pos hε),hc] with r hr hc
  linarith

end InvariantIsing

end

end OAI
