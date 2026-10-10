import OAI.Analysis.MetricEntropy.EntropyFinal
import OAI.Analysis.MetricEntropy.FormCardinality
import OAI.Analysis.MetricEntropy.Construction
import OAI.Analysis.MetricEntropy.EntropyPairLimits
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Counterexamples to metric-entropy duality

The construction supplies actual finite-dimensional bodies and
their least covering numbers from only the numerical parameters. The public
statements retain arbitrary ambient translation centers and the literal polar.
-/

noncomputable section

namespace MetricEntropyDuality

open Filter Topology
open scoped Pointwise

private theorem entropyBudget_lt_of_rank {a b : ℝ} {r : ℕ}
    (hb : 1 ≤ b)
    (hrank : 8 * b * (compressionRadius a : ℝ) ^ 2 *
      (pivotSlots (accuracy a) : ℝ) <
        (r : ℝ) + (compressionRadius a : ℝ) - 1) :
    entropyBudget a r (8 * b) < 1 / (2 * b) := by
  have hb0 : 0 < b := by linarith only [hb]
  have hden : 0 < (r : ℝ) + (compressionRadius a : ℝ) - 1 :=
    lt_of_le_of_lt (by positivity) hrank
  have hfirst : 2 * (compressionRadius a : ℝ) ^ 2 *
      (pivotSlots (accuracy a) : ℝ) /
        ((r : ℝ) + (compressionRadius a : ℝ) - 1) < 1 / (4 * b) := by
    apply (div_lt_div_iff₀ hden (by positivity)).mpr
    nlinarith only [hrank]
  calc
    entropyBudget a r (8 * b) < 1 / (4 * b) + 2 / (8 * b) :=
      add_lt_add_of_lt_of_le hfirst (le_refl _)
    _ = 1 / (2 * b) := by field_simp [ne_of_gt hb0]; ring

/-- The strict counterexample together with actual finite-cover witnesses on
both sides. Thus no empty-infimum convention is used for these numbers. -/
theorem exists_entropy_duality_counterexample_with_covers
    (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ n : ℕ, 0 < n ∧ ∃ K : Set (RealSpace (Fin n)),
      IsSymmetricConvexBody K ∧
      Coverable K (cube (Fin n)) ∧
      Coverable (polar (cube (Fin n))) (a⁻¹ • polar K) ∧
      b * Real.log (coveringNumber (polar (cube (Fin n))) (a⁻¹ • polar K) : ℝ) <
        Real.log (coveringNumber K (cube (Fin n)) : ℝ) := by
  obtain ⟨r, hr, hrank⟩ := exists_rank b (accuracy a) (compressionRadius_pos a)
  have hb0 : 0 < b := by linarith only [hb]
  let P : EntropyPair a r (8 * b) := Classical.choice
    (exists_entropy_pair_with_budget a ha r (Nat.succ_le_of_lt hr)
      (8 * b) (by positivity))
  refine ⟨P.dimension, P.dimension_pos, P.body, P.body_isSymmetricConvexBody,
    P.primal_coverable, P.dual_coverable, ?_⟩
  have hratio : entropyRatio a P.body < 1 / (2 * b) :=
    P.ratio_lt.trans (entropyBudget_lt_of_rank hb hrank)
  have hcross := (div_lt_div_iff₀ P.primal_log_pos
    (by positivity : 0 < 2 * b)).mp hratio
  nlinarith only [hcross, P.primal_log_pos]

/-- For every proposed real pair of duality constants, an actual
full-dimensional symmetric compact convex body violates the inequality with
the standard cube as covering body. -/
theorem exists_entropy_duality_counterexample
    (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ n : ℕ, 0 < n ∧ ∃ K : Set (RealSpace (Fin n)),
      IsSymmetricConvexBody K ∧
      Real.log (coveringNumber K (cube (Fin n)) : ℝ) >
        b * Real.log (coveringNumber (polar (cube (Fin n))) (a⁻¹ • polar K) : ℝ) := by
  obtain ⟨n, hn, K, hK, _, _, hlt⟩ :=
    exists_entropy_duality_counterexample_with_covers a b ha hb
  exact ⟨n, hn, K, hK, hlt⟩

/-- For each fixed scale, the actual polar-to-primal logarithmic entropy
ratio tends to zero along a family of growing positive dimensions. -/
theorem exists_entropy_ratio_family (a : ℝ) (ha : 1 ≤ a) :
    ∃ n : ℕ → ℕ, (∀ j, 0 < n j) ∧
      ∃ K : (j : ℕ) → Set (RealSpace (Fin (n j))),
        (∀ j, IsSymmetricConvexBody (K j) ∧
          Coverable (K j) (cube (Fin (n j))) ∧
          Coverable (polar (cube (Fin (n j)))) (a⁻¹ • polar (K j)) ∧
          0 < Real.log (coveringNumber (K j) (cube (Fin (n j))) : ℝ) ∧
          0 ≤ entropyRatio a (K j)) ∧
        Tendsto n atTop atTop ∧
        Tendsto (fun j => entropyRatio a (K j)) atTop (𝓝 0) := by
  let P : ∀ j : ℕ, EntropyPair a (j + 1) ((j + 1 : ℕ) : ℝ) := fun j =>
    Classical.choice (exists_entropy_pair_with_budget a ha (j + 1)
      (Nat.succ_le_succ (Nat.zero_le j)) ((j + 1 : ℕ) : ℝ)
      (Nat.cast_pos.mpr (Nat.succ_pos j)))
  refine ⟨fun j => (P j).dimension, fun j => (P j).dimension_pos,
    fun j => (P j).body, ?_, EntropyPair.family_dimension_atTop P,
    EntropyPair.family_ratio_tendsto_zero P⟩
  intro j
  exact ⟨(P j).body_isSymmetricConvexBody, (P j).primal_coverable,
    (P j).dual_coverable, (P j).primal_log_pos, (P j).ratio_nonneg⟩

end MetricEntropyDuality

end

end OAI
