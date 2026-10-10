import OAI.Probability.ContinuumTransition.ConvexUniform

namespace OAI

universe u_1

section
open scoped Topology
open Set Filter
namespace ContinuumTemperature

lemma eventually_of_subseq (P : ℕ → Prop)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ n in atTop, P (φ (ψ n))) :
    ∀ᶠ n in atTop, P n := by
  by_contra hh
  obtain ⟨φ,hφ,hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hh)
  obtain ⟨ψ,_,hgood⟩ := h φ hφ
  obtain ⟨n,hn⟩ := hgood.exists
  exact hbad (ψ n) hn

lemma metric_tendsto_of_subseq {E : Type u_1} [PseudoMetricSpace E] {u : ℕ → E} {x : E}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun n => u (φ (ψ n))) atTop (𝓝 x)) : Tendsto u atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hh : ∀ᶠ n in atTop, dist (u n) x < ε := by
    apply eventually_of_subseq
    intro φ hφ
    obtain ⟨ψ,hψ,ht⟩ := h φ hφ
    exact ⟨ψ,hψ,ht.eventually (Metric.ball_mem_nhds x hε)⟩
  exact eventually_atTop.mp hh

end ContinuumTemperature
end

end OAI
