import OAI.Probability.LatticePassage.Stationarity
import Mathlib.Analysis.Subadditive

namespace OAI

namespace CompanionFPP
open MeasureTheory Filter Topology

noncomputable def meanPassageSequence (x : Vertex) (n : ℕ) : ℝ :=
  ∫ ω : Environment, passageTime ω 0 (scaleVertex n x) ∂environmentLaw

lemma scaleVertex_add (m n : ℕ) (x : Vertex) :
    scaleVertex (m+n) x = scaleVertex m x + scaleVertex n x := by
  ext <;> simp [scaleVertex, add_mul]

lemma meanPassageSequence_nonneg (x : Vertex) (n : ℕ) :
    0 ≤ meanPassageSequence x n := by
  apply integral_nonneg_of_ae
  filter_upwards [passageTime_properties] with ω hω
  exact hω.1 _ _

theorem meanPassageSequence_subadditive (x : Vertex) :
    Subadditive (meanPassageSequence x) := by
  intro m n
  unfold meanPassageSequence
  rw [scaleVertex_add]
  exact mean_passageTime_subadditive (scaleVertex m x) (scaleVertex n x)

lemma meanPassageSequence_bddBelow (x : Vertex) :
    BddBelow (Set.range (fun n : ℕ => meanPassageSequence x n / n)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨n,rfl⟩
  exact div_nonneg (meanPassageSequence_nonneg x n) (Nat.cast_nonneg _)

noncomputable def directionalMeanConstant (x : Vertex) : ℝ :=
  (meanPassageSequence_subadditive x).lim

theorem meanPassageSequence_tendsto (x : Vertex) :
    Tendsto (fun n : ℕ => meanPassageSequence x n / n) atTop (𝓝 (directionalMeanConstant x)) :=
  (meanPassageSequence_subadditive x).tendsto_lim (meanPassageSequence_bddBelow x)

theorem directionalMeanConstant_nonneg (x : Vertex) : 0 ≤ directionalMeanConstant x :=
  ge_of_tendsto (meanPassageSequence_tendsto x) (Filter.Eventually.of_forall
    (fun n => div_nonneg (meanPassageSequence_nonneg x n) (Nat.cast_nonneg _)))

theorem directionalMeanConstant_le_mean (x : Vertex) :
    directionalMeanConstant x ≤ ∫ ω : Environment, passageTime ω 0 x ∂environmentLaw := by
  have h := (meanPassageSequence_subadditive x).lim_le_div
    (meanPassageSequence_bddBelow x) (n := 1) (by norm_num)
  simpa [meanPassageSequence, directionalMeanConstant, scaleVertex] using h

end CompanionFPP

end OAI
