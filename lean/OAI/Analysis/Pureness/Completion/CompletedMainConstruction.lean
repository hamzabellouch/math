import OAI.Analysis.Pureness.Completion.CompletedBlockSeries
import OAI.Analysis.Pureness.Completion.CompletedIncrementApproximation
import OAI.Analysis.Pureness.Divisibility.ExtendedRankBudget
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma increment_partial_budget (u r η : ℕ → ℝ) (s : ℝ) (hu : u 0 = 0)
    (h : ∀ j, 0 ≤ s * u (j + 1) - s * u j - r j ∧ s * u (j + 1) - s * u j - r j ≤ η j)
    (q : ℕ) :
    (∑ j ∈ Finset.range q, r j) ≤ s * u q ∧
      s * u q ≤ (∑ j ∈ Finset.range q, r j) + ∑ j ∈ Finset.range q, η j := by
  induction q with
  | zero => simp [hu]
  | succ q ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    constructor <;> linarith [(h q).1, (h q).2]

theorem exists_completed_rank_budget (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (a : CornerCompletion A) (ha : 0 ≤ a) (s : ℝ) (hs : 0 ≤ s)
    (η : ℕ → ℝ) (hη : ∀ j, 0 < η j) (hηsum : Summable η) :
    ∃ b : CornerCompletion A, 0 ≤ b ∧ ∀ τ : TracialState A,
      completedRootRank τ b ≤ ENNReal.ofReal s * completedRootRank τ a ∧
      ENNReal.ofReal s * completedRootRank τ a ≤ completedRootRank τ b + ENNReal.ofReal (∑' j, η j) := by
  let δ : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ (j + 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδsum : Summable δ := by
    have hh : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    simpa only [δ, pow_succ] using hh.mul_right (1 / 2 : ℝ)
  obtain ⟨l, w, hw, hn, he⟩ := exists_completed_increment_approximants hsimple hinf hT a ha s hs η δ hη hδ
  have hnorm : Summable (fun j => ‖w j‖) := Summable.of_nonneg_of_le (fun j => norm_nonneg _) hn hδsum
  let : ∀ j, NeZero (l j + 1) := fun j => inferInstance
  obtain ⟨b, hb, _, hbr⟩ := exists_completedBlockSum (fun j => l j + 1) w hw hnorm
  refine ⟨b, hb, fun τ => ?_⟩
  let u : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal (τ.functional (completedSourceU a q)).re
  let r : ℕ → ℝ≥0∞ := fun q => ∑ j ∈ Finset.range q, matrixRank τ (w j)
  let e : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal (∑ j ∈ Finset.range q, η j)
  have hsumrank (q : ℕ) : ENNReal.ofReal (∑ j ∈ Finset.range q, (matrixRank τ (w j)).toReal) = r q := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
    apply Finset.sum_congr rfl
    intro j _
    exact ENNReal.ofReal_toReal (matrixRank_ne_top τ (w j) (hw j))
  have hpartial (q : ℕ) := increment_partial_budget
    (fun j => (τ.functional (completedSourceU a j)).re)
    (fun j => (matrixRank τ (w j)).toReal) η s (by simp [completedSourceU]) (fun j => he j τ) q
  have hlow (q : ℕ) : r q ≤ ENNReal.ofReal s * u q := by
    rw [← hsumrank q, ← ENNReal.ofReal_mul hs]
    exact ENNReal.ofReal_le_ofReal (hpartial q).1
  have hupp (q : ℕ) : ENNReal.ofReal s * u q ≤ r q + e q := by
    rw [← hsumrank q, ← ENNReal.ofReal_mul hs, ← ENNReal.ofReal_add
      (Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg) (Finset.sum_nonneg fun j _ => (hη j).le)]
    exact ENNReal.ofReal_le_ofReal (hpartial q).2
  have herr (q : ℕ) : e q ≤ ENNReal.ofReal (∑' j, η j) :=
    ENNReal.ofReal_le_ofReal (Summable.sum_le_tsum (Finset.range q) (fun j _ => (hη j).le) hηsum)
  have hbudget := extended_rank_budget u r e (ENNReal.ofReal s) (ENNReal.ofReal (∑' j, η j)) hlow hupp herr
  have hu : (⨆ q, u q) = completedRootRank τ a := completedSourceU_trace_iSup τ a ha
  have hr : (⨆ q, r q) = completedRootRank τ b := by
    rw [hbr τ, ENNReal.tsum_eq_iSup_nat]
  rwa [hu, hr] at hbudget
end CuntzPureness

end

end OAI
