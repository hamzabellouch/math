import OAI.Analysis.CircleDomains.Topology.CompactPathApproximationStep
import OAI.Analysis.CircleDomains.Topology.IteratedPathApproximation

namespace OAI

/-! Compact locally connected subsets of a Banach space have uniformly
small paths. Successive ambient replacements converge inside the set. -/
open Set Function Filter Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma compact_uniform_local_paths
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : IsCompact K) [LocallyConnectedSpace K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
      ∃ β : Path x y, (∀ t, β t ∈ K) ∧ ∀ t, dist (β t) x < ε := by
  obtain ⟨δ, hδ, hlocal⟩ := uniform_local_approximate_paths hK (show 0 < ε / 2 by linarith)
  let d : ℕ → ℝ := fun n => (ε / 8) * (1 / 2 : ℝ)^n
  have hdpos : ∀ n, 0 < d n := fun n => by dsimp [d]; positivity
  have hdsum : Summable d := summable_geometric_two.mul_left (ε / 8)
  have hdval : (∑' n, d n) = ε / 4 := by
    rw [show d = fun n => (ε / 8) * (1 / 2 : ℝ)^n by rfl, tsum_mul_left, tsum_geometric_two]
    ring
  choose ρ hρpos hreplace using fun n => compact_path_approximation_step hK (hdpos n)
  let τ : ℕ → ℝ := fun n => min (ρ n) (1 / (n + 1 : ℝ))
  have hτpos : ∀ n, 0 < τ n := fun n => lt_min (hρpos n) (by positivity)
  have hτlim : Tendsto τ atTop (𝓝 0) :=
    squeeze_zero (fun n => (hτpos n).le) (fun n => min_le_right _ _)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  obtain ⟨γ₀, hγ₀diam, hγ₀near⟩ := hlocal x hx y hy hxy (τ 0) (hτpos 0)
  have hstep : ∀ n, ∀ γ : Path x y,
      (∀ t, ∃ c ∈ K, dist (γ t) c < τ n) →
      ∃ β : Path x y, (∀ t, dist (γ t) (β t) ≤ d n) ∧
        (∀ t, ∃ c ∈ K, dist (β t) c < τ (n + 1)) := by
    intro n γ hn
    have hn' : ∀ t, ∃ c ∈ K, dist (γ t) c < ρ n := by
      intro t
      obtain ⟨c, hc, htc⟩ := hn t
      exact ⟨c, hc, htc.trans_le (min_le_left _ _)⟩
    obtain ⟨β, hβ, hβK⟩ := hreplace n x hx y hy γ hn' (τ (n + 1)) (hτpos (n + 1))
    exact ⟨β, fun t => by simpa only [dist_comm] using (hβ t).le, hβK⟩
  obtain ⟨β, hβK, hβ⟩ := iterate_path_approximations hK.isClosed d τ hdsum
    (fun n => (hdpos n).le) hτlim γ₀ hγ₀near hstep
  refine ⟨β, hβK, ?_⟩
  intro t
  have ht := hβ t
  rw [hdval, dist_comm] at ht
  have ht₀ := hγ₀diam t
  have htri := dist_triangle (β t) (γ₀ t) x
  linarith

end CircleDomainRigidity

end

end OAI
