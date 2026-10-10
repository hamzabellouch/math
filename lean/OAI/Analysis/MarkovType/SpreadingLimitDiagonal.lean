import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace.Real

namespace OAI

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

theorem exists_common_subsequence_of_bounded_with_bounds
    {Q : Type*} [Countable Q] (v : ℕ → Q → ℝ) (b : Q → ℝ)
    (hbound : ∀ n q, v n q ∈ Set.Icc 0 (b q)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ l : Q → ℝ,
      (∀ q, l q ∈ Set.Icc 0 (b q)) ∧
      ∀ q, Tendsto (fun n => v (σ n) q) atTop (𝓝 (l q)) := by
  let x : ℕ → (∀ q : Q, Set.Icc (0 : ℝ) (b q)) :=
    fun n q => ⟨v n q, hbound n q⟩
  obtain ⟨a, σ, hσ, ha⟩ := CompactSpace.tendsto_subseq x
  refine ⟨σ, hσ, (fun q => (a q : ℝ)), (fun q => (a q).property), ?_⟩
  intro q
  have hcoord : Continuous
      (fun z : (∀ r : Q, Set.Icc (0 : ℝ) (b r)) => (z q : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply q)
  simpa only [Function.comp_def, x] using (hcoord.tendsto a).comp ha

theorem exists_common_subsequence_of_bounded
    {Q : Type*} [Countable Q] (v : ℕ → Q → ℝ) (b : Q → ℝ)
    (hbound : ∀ n q, v n q ∈ Set.Icc 0 (b q)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ q, ∃ l : ℝ, Tendsto (fun n => v (σ n) q) atTop (𝓝 l) := by
  obtain ⟨σ, hσ, l, _, hl⟩ :=
    exists_common_subsequence_of_bounded_with_bounds v b hbound
  exact ⟨σ, hσ, fun q => ⟨l q, hl q⟩⟩

end MarkovSuperreflexivity

end OAI
