import OAI.Combinatorics.Ryser.Selection.Quantitative
import OAI.Combinatorics.Ryser.Selection.Parameters
import OAI.Combinatorics.Ryser.Selection.NumericLimits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

universe u

namespace RyserCoveringCounterexample.Selection

theorem compatible_selection_uniform (D : ℕ) (hD : 1 ≤ D) :
    ∃ K : ℕ, 6 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ∃ Q : ℕ,
        ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
          (n : ℕ) (data : Data F n),
          Bounded D data → Q ≤ Fintype.card F →
            1 - ε ≤ (poolLaw F n K).prob
              (fun pool => HasCompatibleChoice data pool) := by
  classical
  obtain ⟨K, hK, hsmall, hlarge⟩ := exists_selection_pool_size D
  refine ⟨K, hK, ?_⟩
  intro ε hε
  obtain ⟨Q0, hQ0⟩ :=
    exists_threshold_selection_failure_bound.{u} D hD K hK hsmall hlarge.le
  have hK3 : 3 < K := lt_of_lt_of_le (by norm_num : 3 < 6) hK
  have hB : (0 : ℝ) < max 1 (selectionLargeCoefficient D K) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨R, _hR, Q1, hQ1⟩ :=
    exists_cutoff_threshold_selectionFailureBound D K
      (selectionSmallCoefficient D K)
      (max 1 (selectionLargeCoefficient D K))
      (equationBound D)
      (densityChunkCount D : ℝ)
      (densityRate D)
      (selectionCutoff D)
      hK3 hB (densityRate_pos D hD) (selectionCutoff_pos D hD) hε
  refine ⟨max Q0 Q1, ?_⟩
  intro F _ _ _ n data hdata hq
  have hq0 : Q0 ≤ Fintype.card F := (le_max_left _ _).trans hq
  have hq1 : Q1 ≤ Fintype.card F := (le_max_right _ _).trans hq
  have hfailure :
      (poolLaw F n K).prob (fun pool => ¬HasCompatibleChoice data pool) < ε :=
    (hQ0 F n data hdata hq0 R).trans_lt (hQ1 (Fintype.card F) hq1)
  rw [(poolLaw F n K).prob_compl (fun pool => HasCompatibleChoice data pool)] at hfailure
  linarith

end RyserCoveringCounterexample.Selection

end OAI
