import OAI.Analysis.CircleDomains.Topology.ClosedSetPathLimit

namespace OAI

/-! Dependent iteration of the proved path replacement step. -/
open Set Function Filter Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma iterate_path_approximations
    {E : Type*} [MetricSpace E] [CompleteSpace E] {K : Set E} (hK : IsClosed K)
    {x y : E} (d ρ : ℕ → ℝ) (hd : Summable d) (hd0 : ∀ n, 0 ≤ d n)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (γ₀ : Path x y) (hγ₀ : ∀ t, ∃ c ∈ K, dist (γ₀ t) c < ρ 0)
    (hstep : ∀ n, ∀ γ : Path x y,
      (∀ t, ∃ c ∈ K, dist (γ t) c < ρ n) →
      ∃ β : Path x y, (∀ t, dist (γ t) (β t) ≤ d n) ∧
        (∀ t, ∃ c ∈ K, dist (β t) c < ρ (n + 1))) :
    ∃ β : Path x y, (∀ t, β t ∈ K) ∧ ∀ t, dist (γ₀ t) (β t) ≤ ∑' n, d n := by
  let Stage (n : ℕ) := {γ : Path x y // ∀ t, ∃ c ∈ K, dist (γ t) c < ρ n}
  have hnext (n : ℕ) (p : Stage n) :
      ∃ q : Stage (n + 1), ∀ t, dist (p.val t) (q.val t) ≤ d n := by
    obtain ⟨β, he, hn⟩ := hstep n p.val p.property
    exact ⟨⟨β, hn⟩, he⟩
  let P : (n : ℕ) → Stage n := fun n => Nat.rec ⟨γ₀, hγ₀⟩ (fun j p => (hnext j p).choose) n
  have hPstep : ∀ n t, dist ((P n).val t) ((P (n + 1)).val t) ≤ d n := by
    intro n t
    exact (hnext n (P n)).choose_spec t
  obtain ⟨β, hβK, hβ⟩ := closed_set_path_limit hK (fun n => (P n).val) d ρ hd hd0 hPstep hρ
    (fun n => (P n).property)
  refine ⟨β, hβK, ?_⟩
  intro t
  simpa only [P, Nat.rec_zero, Nat.zero_add] using hβ 0 t

end CircleDomainRigidity

end

end OAI
