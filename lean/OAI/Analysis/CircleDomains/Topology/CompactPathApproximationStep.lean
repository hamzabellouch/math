import OAI.Analysis.CircleDomains.Topology.LocalApproximatePaths
import OAI.Analysis.CircleDomains.Topology.DyadicPathReplacement

namespace OAI

/-! A path close to a compact locally connected set can be replaced,
with fixed endpoints and small uniform error, by a path arbitrarily closer
to that set. This is the step iterated to obtain an actual path in the set. -/
open Set Function Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma path_near_set_selector {E : Type*} [MetricSpace E] {K : Set E}
    {x y : E} (γ : Path x y) (hx : x ∈ K) (hy : y ∈ K) {τ : ℝ} (hτ : 0 < τ)
    (hnear : ∀ t, ∃ c ∈ K, dist (γ t) c < τ) :
    ∃ k : I → E, (∀ t, k t ∈ K) ∧ k 0 = x ∧ k 1 = y ∧
      ∀ t, dist (γ t) (k t) < τ := by
  classical
  let k : I → E := fun t => if t = 0 then x else if t = 1 then y else (hnear t).choose
  refine ⟨k, ?_, by simp [k], by simp [k], ?_⟩
  · intro t
    by_cases h0 : t = 0
    · simp only [k, ite_eq_left h0]
      exact hx
    · by_cases h1 : t = 1
      · simp only [k, ite_eq_right h0, ite_eq_left h1]
        exact hy
      · simp only [k, ite_eq_right h0, ite_eq_right h1]
        exact (hnear t).choose_spec.1
  · intro t
    by_cases h0 : t = 0
    · subst t
      simpa [k] using hτ
    · by_cases h1 : t = 1
      · subst t
        simpa [k] using hτ
      · simp only [k, ite_eq_right h0, ite_eq_right h1]
        exact (hnear t).choose_spec.2

lemma compact_path_approximation_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) [LocallyConnectedSpace K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ K, ∀ γ : Path x y,
      (∀ t, ∃ c ∈ K, dist (γ t) c < ρ) →
      ∀ η : ℝ, 0 < η → ∃ β : Path x y,
        (∀ t, dist (β t) (γ t) < ε) ∧ (∀ t, ∃ c ∈ K, dist (β t) c < η) := by
  obtain ⟨δ, hδ, hlocal⟩ := uniform_local_approximate_paths hK (show 0 < ε / 4 by linarith)
  let ρ := min (δ / 4) (ε / 4)
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρδ : 3 * ρ ≤ δ := by
    have h := min_le_left (δ / 4) (ε / 4)
    dsimp [ρ]
    linarith
  have hρε : ε / 4 + 2 * ρ < ε := by
    have h := min_le_right (δ / 4) (ε / 4)
    dsimp [ρ]
    linarith
  refine ⟨ρ, hρ, ?_⟩
  intro x hx y hy γ hnear η hη
  obtain ⟨k, hk, hk0, hk1, hγk⟩ := path_near_set_selector γ hx hy hρ hnear
  obtain ⟨n, hosc⟩ := exists_dyadicSmallOscillation γ.continuous hρ
  have hjoin : ∀ a ∈ K, ∀ b ∈ K, dist a b < δ →
      ∃ β : Path a b, (∀ t, dist (β t) a < ε / 4) ∧
        (∀ t, ∃ c ∈ K, dist (β t) c < η) := fun a ha b hb hab =>
    hlocal a ha b hb hab η hη
  have h := dyadic_path_replacement hρδ hjoin n γ k hk hosc hγk
  rw [hk0, hk1] at h
  obtain ⟨β, hβ, hβK⟩ := h
  exact ⟨β, fun t => (hβ t).trans hρε, hβK⟩

end CircleDomainRigidity

end

end OAI
