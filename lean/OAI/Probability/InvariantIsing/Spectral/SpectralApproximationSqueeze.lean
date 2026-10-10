import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace OAI

/-! The final two-scale squeeze used in compact spectral approximation. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

lemma spectral_approximation_squeeze (p : ℕ → ℝ) (lo hi : ℕ → ℕ → ℝ)
    (v δ : ℕ → ℝ) (L : ℝ) (hv : Tendsto v atTop (𝓝 L))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hlo : ∀ k, Tendsto (lo k) atTop (𝓝 (v k)))
    (hhi : ∀ k, Tendsto (hi k) atTop (𝓝 (v k)))
    (hbound : ∀ k, ∀ᶠ N in atTop, lo k N-δ k/2 ≤ p N ∧ p N ≤ hi k N+δ k/2) :
    Tendsto p atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk,hdk⟩ := ((Metric.tendsto_nhds.mp hv (ε/3) (by positivity)).and
    (Metric.tendsto_nhds.mp hδ (ε/3) (by positivity))).exists
  filter_upwards [Metric.tendsto_nhds.mp (hlo k) (ε/3) (by positivity),
    Metric.tendsto_nhds.mp (hhi k) (ε/3) (by positivity),hbound k] with N hl hu hp
  rw [Real.dist_eq,abs_lt] at hk hdk hl hu ⊢
  constructor <;> linarith

end InvariantIsing

end

end OAI
