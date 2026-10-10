import OAI.Combinatorics.ProgressionColoring.GlobalLabelWords
import OAI.Combinatorics.ProgressionColoring.UniformMesh
import OAI.Combinatorics.ProgressionColoring.AdaptiveMesh

namespace OAI

namespace QuantitativeVanDerWaerden

noncomputable section

/-- The actual uniform mesh, with no extra partition hypothesis. -/
def uniformPartition (n : ℕ) (hn : 0 < n) : CirclePartition (Fin n) where
  left := UniformMesh.left n
  right := UniformMesh.right n
  left_nonneg := UniformMesh.left_nonneg n
  left_lt_right := UniformMesh.left_lt_right n hn
  right_le_one := UniformMesh.right_le_one n hn
  covers := fun x hx => UniformMesh.existsUnique_contains n hn x hx

theorem uniformPartition_label (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (uniformPartition n hn).label x = UniformMesh.label n hn x := by
  apply (uniformPartition n hn).label_eq_of_mem
  exact UniformMesh.label_mem n hn x

/-- The actual centered adaptive mesh, translated to the shared fundamental
interval. This is a translation of cells, not an identification of labels. -/
def adaptivePartition (A : AdaptiveMesh) : CirclePartition A.Label where
  left := fun i => A.left i + 1 / 2
  right := fun i => A.right i + 1 / 2
  left_nonneg := fun i => by linarith [A.left_ge_neg_half i]
  left_lt_right := fun i => by
    have h := A.width_pos i
    dsimp [AdaptiveMesh.width] at h
    linarith
  right_le_one := fun i => by linarith [A.right_le_half i]
  covers := by
    intro x hx
    obtain ⟨i, hi⟩ := A.exists_label
      (show -(1 / 2 : ℝ) ≤ x - 1 / 2 by linarith [hx.1])
      (show x - 1 / 2 < 1 / 2 by linarith [hx.2])
    refine ⟨i, ?_, ?_⟩
    · change A.left i + 1 / 2 ≤ x ∧ x < A.right i + 1 / 2
      rcases hi with ⟨hil, hir⟩
      constructor <;> linarith
    · intro j hj
      apply A.label_unique j i (x := x - 1 / 2) _ hi
      change A.left j ≤ x - 1 / 2 ∧ x - 1 / 2 < A.right j
      constructor <;> linarith [hj.1, hj.2]

theorem adaptivePartition_label (A : AdaptiveMesh) (x : ℝ) :
    (adaptivePartition A).label (x + 1 / 2) = A.meshLabel x := by
  apply (adaptivePartition A).label_eq_of_mem
  have h := A.meshLabel_contains x
  change A.left (A.meshLabel x) ≤ centered x ∧
    centered x < A.right (A.meshLabel x) at h
  change A.left (A.meshLabel x) + 1 / 2 ≤ Int.fract (x + 1 / 2) ∧
    Int.fract (x + 1 / 2) < A.right (A.meshLabel x) + 1 / 2
  have heq : Int.fract (x + 1 / 2) = centered x + 1 / 2 := by
    change (x + 1 / 2) - (⌊x + 1 / 2⌋ : ℝ) =
      (x - (⌊x + 1 / 2⌋ : ℝ)) + 1 / 2
    ring
  rw [heq]
  constructor <;> linarith [h.1, h.2]

end
end QuantitativeVanDerWaerden

end OAI
