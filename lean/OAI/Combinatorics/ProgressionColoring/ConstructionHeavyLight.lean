import OAI.Combinatorics.ProgressionColoring.ConstructionModel
import OAI.Combinatorics.ProgressionColoring.OuterWordTests
import OAI.Combinatorics.ProgressionColoring.LongPeriodColoring

namespace OAI

/-!
# Heavy and light positions in the actual construction

The real-valued heavy threshold used in the block argument and the integer
light threshold used in the outer word tests classify exactly the same
positions. Both multiplicities count the entire literal progression word.
-/

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters
open scoped Classical

theorem real_heavy_iff (k M m : ℕ) (hM : 0 < M) :
    (k : ℝ) / (M : ℝ) < (m : ℝ) ↔ k < M * m := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [div_lt_iff₀ hM', mul_comm]
  norm_cast

theorem not_real_heavy_iff (k M m : ℕ) (hM : 0 < M) :
    ¬ ((k : ℝ) / (M : ℝ) < (m : ℝ)) ↔ M * m ≤ k := by
  rw [real_heavy_iff k M m hM, not_lt]

variable {k : ℕ}

theorem literalProgressionHeavy_iff_word_heavy (s : Data k) (hk : 3 ≤ k)
    (a d : Group s) (j : Fin k) :
    literalProgressionHeavy (mesh s hk) s.q (dimension k) (lambda k)
      (uniformCount k) k (uniformCount_pos hk) a d (cutoff k) j ↔
    k < cutoff k * OuterWordTests.multiplicity (fullLabelWord s hk (a, d))
      (fullLabelWord s hk (a, d) j) := by
  unfold literalProgressionHeavy
  rw [real_heavy_iff k (cutoff k) _ (cutoff_pos (by omega : 1 ≤ k))]
  unfold OuterWordTests.multiplicity
  apply Iff.of_eq
  apply congrArg (fun n : ℕ => k < cutoff k * n)
  apply congrArg (Finset.card : Finset (Fin k) → ℕ)
  apply Finset.ext
  intro i
  constructor
  · intro hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [fullLabelWord, fullLabel, nsmul_eq_mul] using (Finset.mem_filter.mp hi).2
  · intro hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [fullLabelWord, fullLabel, nsmul_eq_mul] using (Finset.mem_filter.mp hi).2

/-- The two literal finite sets of light positions agree. -/
theorem selected_lightPositions_eq (s : Data k) (hk : 3 ≤ k) (a d : Group s) :
    BlockCoverage.lightPositions
      (literalProgressionHeavy (mesh s hk) s.q (dimension k) (lambda k)
        (uniformCount k) k (uniformCount_pos hk) a d (cutoff k)) =
      OuterWordTests.lightPositions (cutoff k) (fullLabelWord s hk (a, d)) := by
  ext j
  simp only [BlockCoverage.lightPositions, Finset.mem_filter, Finset.mem_univ,
    true_and, OuterWordTests.mem_lightPositions,
    literalProgressionHeavy_iff_word_heavy, not_lt]

/-- The block-coverage light count is exactly the outer-test light count. -/
theorem selected_lightCount_eq (s : Data k) (hk : 3 ≤ k) (a d : Group s) :
    BlockCoverage.lightCount
      (literalProgressionHeavy (mesh s hk) s.q (dimension k) (lambda k)
        (uniformCount k) k (uniformCount_pos hk) a d (cutoff k)) =
      (OuterWordTests.lightPositions (cutoff k) (fullLabelWord s hk (a, d))).card := by
  unfold BlockCoverage.lightCount
  rw [selected_lightPositions_eq]

/-- Failure of the many-light-positions branch supplies the real light-count
bound required by the long-period coloring theorem. -/
theorem selected_lightCount_le_of_few (s : Data k) (hk : 3 ≤ k) (a d : Group s)
    (hfew : ¬ k ≤ 10 *
      (OuterWordTests.lightPositions (cutoff k) (fullLabelWord s hk (a, d))).card) :
    (BlockCoverage.lightCount
      (literalProgressionHeavy (mesh s hk) s.q (dimension k) (lambda k)
        (uniformCount k) k (uniformCount_pos hk) a d (cutoff k)) : ℝ) ≤
      (k : ℝ) / 10 := by
  rw [selected_lightCount_eq]
  have hn : 10 *
      (OuterWordTests.lightPositions (cutoff k) (fullLabelWord s hk (a, d))).card < k :=
    Nat.lt_of_not_ge hfew
  have hr : (10 : ℝ) *
      ((OuterWordTests.lightPositions (cutoff k) (fullLabelWord s hk (a, d))).card : ℝ) <
      (k : ℝ) := by exact_mod_cast hn
  linarith

end QuantitativeVanDerWaerden.ConstructionModel

end OAI
