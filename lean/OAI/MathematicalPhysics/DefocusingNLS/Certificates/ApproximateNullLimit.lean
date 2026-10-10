import OAI.MathematicalPhysics.DefocusingNLS.Certificates.UniformCutoffLimit

namespace OAI

/-! # Preservation of a null limit under arbitrarily close null approximations -/

open Filter Topology

namespace DefocusingNLS

theorem tendsto_zero_of_null_approximations {E : Type*} [SeminormedAddCommGroup E]
    (f : ℕ → E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : ℕ → E, Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ‖f n - g n‖ ≤ ε) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hclose⟩ := happrox (ε / 2) (by positivity)
  have hs : ∀ᶠ n in atTop, ‖g n‖ < ε / 2 := by
    obtain ⟨n₁, hn₁⟩ := Metric.tendsto_atTop.mp hg (ε / 2) (by positivity)
    exact eventually_atTop.2 ⟨n₁, fun n hn => by
      simpa only [dist_zero_right] using hn₁ n hn⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hclose.and hs)
  refine ⟨n₀, ?_⟩
  intro n hn
  rw [dist_zero_right]
  have h := hn₀ n hn
  calc
    ‖f n‖ ≤ ‖f n - g n‖ + ‖g n‖ := norm_le_norm_sub_add _ _
    _ < ε := by linarith [h.1, h.2]

end DefocusingNLS

end OAI
