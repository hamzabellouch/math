import OAI.Probability.InvariantIsing.Cavity.CavityCappedLogLimit
import OAI.Probability.InvariantIsing.Cavity.CavityRadiusRemoval

namespace OAI

/-! The order of limits in the cavity argument: pass to the finite-replica
limit at each fixed cutoff, then remove the cutoff with a uniform error. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_remove_cutoff_limit (f : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (a e : ℕ → ℝ)
    (L : ℝ) (he : Tendsto e atTop (𝓝 0))
    (hg : ∀ k, Tendsto (g k) atTop (𝓝 (a k)))
    (hfg : ∀ k, ∀ᶠ n in atTop, |f n - g k n| ≤ e k)
    (ha : ∀ k, |a k - L| ≤ e k) : Tendsto f atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := (he.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  have hclose := (hg k).eventually (Metric.ball_mem_nhds (a k) (show 0 < ε / 3 by positivity))
  filter_upwards [hfg k, hclose] with n hn hgn
  rw [Real.dist_eq] at hgn ⊢
  calc
    |f n - L| ≤ |f n - g k n| + |g k n - L| := abs_sub_le _ _ _
    _ ≤ |f n - g k n| + (|g k n - a k| + |a k - L|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ < ε := by linarith [ha k]

end InvariantIsing

end

end OAI
