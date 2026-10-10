import Mathlib
import OAI.Computability.VertexCover.Reduction.SeparatorStarOscillation
import OAI.Computability.VertexCover.Analysis.SeparatorRoundingErrorAe

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

theorem query_splice_outside (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (hidden : Φ.HiddenSeeds J) (j : Fin d) (hj : j ∉ J) :
    Φ.query (Φ.spliceSeeds J frozen hidden) j = Φ.query frozen j := by
  classical
  apply Φ.query_eq_of_questions
  · intro k h
    have hn : (⟨(j,k),h⟩ : PositionPair d) ∉ internalPairs J := by
      simp [internalPairs, hj]
    simp [spliceSeeds, hn]
  · intro k h
    have hn : (⟨(k,j),h⟩ : PositionPair d) ∉ internalPairs J := by
      simp [internalPairs, hj]
    simp [spliceSeeds, hn]

noncomputable def spliceWeights (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Fin d → Fin (Φ.WeightDimension d) → ℝ) (s : Φ.BatchWeights J) :
      Fin d → Fin (Φ.WeightDimension d) → ℝ := by
  classical
  exact fun j => if h : j ∈ J then s ⟨j,h⟩ else frozen j

noncomputable def outsideSum (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (weights : Fin d → Fin (Φ.WeightDimension d) → ℝ) :
    Φ.Coordinate d → ℝ := ∑ j ∈ Jᶜ, Φ.increment (Φ.query frozen j) (weights j)

theorem continuousSum_splice (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (weights : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) :
    Φ.continuousSum (Φ.spliceSeeds J frozen hidden) (Φ.spliceWeights J weights s) =
      Φ.outsideSum J frozen weights + Φ.batchSum (Φ.spliceSeeds J frozen hidden) J s := by
  classical
  unfold continuousSum outsideSum batchSum
  rw [← Finset.sum_add_sum_compl J]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hnj : j ∉ J := Finset.mem_compl.mp hj
    simp only [spliceWeights, dite_eq_right hnj, Φ.query_splice_outside J frozen hidden j hnj]
  · rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j _
    simp only [spliceWeights, dite_eq_left j.2]

theorem batchFunction_is_restriction (Φ : LabelCover) {d : ℕ} (J : Finset (Fin d))
    (frozen : Φ.Seeds d) (weights : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty)
    (hidden : Φ.HiddenSeeds J) (s : Φ.BatchWeights J) :
    Φ.batchFunction (Φ.spliceSeeds J frozen hidden) J (Φ.outsideSum J frozen weights) A hA s =
      Φ.separator A hA (Φ.continuousSum (Φ.spliceSeeds J frozen hidden)
        (Φ.spliceWeights J weights s)) := by
  rw [Φ.continuousSum_splice]
  rfl

theorem separator_bound_on_cube (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) (hs : Φ.InWeightCube s) :
    |Φ.separator A hA (Φ.continuousSum seed s)| ≤ d := by
  have hzero : Φ.continuousSum seed 0 = 0 := by
    change Φ.continuousSumCLM seed 0 = 0
    exact map_zero _
  have hl := Φ.separator_lipschitz A hA (Φ.continuousSum seed s) 0
  have hn := Φ.continuousSum_close seed s 0 (by norm_num : (0:ℝ)≤1)
    (by simpa only [InWeightCube, Pi.zero_apply, sub_zero] using hs)
  rw [hzero] at hn
  simpa only [Φ.separator_zero, sub_zero, mul_one] using hl.trans hn

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
