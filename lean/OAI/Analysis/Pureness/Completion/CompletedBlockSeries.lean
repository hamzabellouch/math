import OAI.Analysis.Pureness.Cuntz.OffsetMatrices

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def completedBlockHom (o k : ℕ) : MatrixStage A k →⋆ₙₐ[ℂ] CornerCompletion A :=
  (completedMatrixInclude A (o + k)).comp (offsetMatrixHom o le_rfl)

lemma completedBlock_isometry (o k : ℕ) : Isometry (completedBlockHom (A := A) o k) :=
  (completedMatrixInclude_isometry A (o + k)).comp
    (NonUnitalStarAlgHom.isometry (offsetMatrixHom (A := A) o (le_rfl : o + k ≤ o + k))
      (offsetMatrixHom_injective o le_rfl))

lemma completedBlock_norm (o k : ℕ) (a : MatrixStage A k) :
    ‖completedBlockHom o k a‖ = ‖a‖ := by
  change ‖completedMatrixInclude A (o + k) (offsetMatrix o le_rfl a)‖ = _
  rw [completedMatrixInclude_norm, offsetMatrix_norm]

lemma completedBlock_nonneg (o k : ℕ) (a : MatrixStage A k) (ha : 0 ≤ a) :
    0 ≤ completedBlockHom o k a := by
  obtain ⟨x, rfl⟩ := positive_square_factor a ha
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

lemma completedBlock_weight (τ : TracialState A) (o k : ℕ) (a : MatrixStage A k) (ha : 0 ≤ a) :
    completedDiagonalWeight τ (completedBlockHom o k a) = ENNReal.ofReal (matrixTrace τ a).re := by
  change completedDiagonalWeight τ (completedMatrixInclude A (o + k) (offsetMatrix o le_rfl a)) = _
  have hp : 0 ≤ offsetMatrix o le_rfl a :=
    (nonUnitalStarAlgHom_nonneg_iff (offsetMatrixHom o le_rfl) (offsetMatrixHom_injective o le_rfl) a).mpr ha
  rw [completedDiagonalWeight_include τ _ _ hp, matrixTrace_offset]

lemma completedBlock_rank (τ : TracialState A) (o k : ℕ) [NeZero k] (a : MatrixStage A k) (ha : 0 ≤ a) :
    completedRootRank τ (completedBlockHom o k a) = matrixRank τ a := by
  apply tendsto_nhds_unique (completed_root_trace_tendsto_rank τ _ (completedBlock_nonneg o k a ha))
  convert matrixPower_trace_tendsto_rank τ a ha using 1
  funext j
  rw [nonUnital_nnrpow_map (completedBlockHom o k) (completedBlock_isometry o k).continuous a ha _ (by positivity)]
  exact completedBlock_weight τ o k (positivePower a (((j : ℝ≥0) + 1)⁻¹)) CFC.nnrpow_nonneg

lemma completedBlock_eq_include (o : ℕ) {k l : ℕ} (h : o + k ≤ l) (a : MatrixStage A k) :
    completedBlockHom o k a = completedMatrixInclude A l (offsetMatrix o h a) := by
  change completedMatrixInclude A (o + k) (offsetMatrix o le_rfl a) = _
  rw [← completedMatrixInclude_corner A h, corner_offsetMatrix]

lemma completedBlock_disjoint (o p : ℕ) {k m : ℕ} (h : o + k ≤ p)
    (a : MatrixStage A k) (b : MatrixStage A m) :
    completedBlockHom o k a * completedBlockHom p m b = 0 := by
  let l := max (o + k) (p + m)
  rw [completedBlock_eq_include o (le_max_left (o + k) (p + m)) a,
    completedBlock_eq_include p (le_max_right (o + k) (p + m)) b, ← map_mul,
    offsetMatrix_disjoint o p _ _ h a b, map_zero]

def blockStart (k : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, k i

lemma blockStart_succ (k : ℕ → ℕ) (j : ℕ) : blockStart k (j + 1) = blockStart k j + k j :=
  Finset.sum_range_succ k j

lemma blockStart_monotone (k : ℕ → ℕ) : Monotone (blockStart k) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [blockStart_succ]
  exact Nat.le_add_right _ _

def completedBlockTerm (k : ℕ → ℕ) (w : (j : ℕ) → MatrixStage A (k j)) (j : ℕ) : CornerCompletion A :=
  completedBlockHom (blockStart k j) (k j) (w j)

lemma completedBlockTerm_orthogonal (k : ℕ → ℕ) (w : (j : ℕ) → MatrixStage A (k j))
    (hw : ∀ j, 0 ≤ w j) (i j : ℕ) (hij : i ≠ j) :
    completedBlockTerm k w i * completedBlockTerm k w j = 0 := by
  have hlt (i j : ℕ) (hij : i < j) : completedBlockTerm k w i * completedBlockTerm k w j = 0 := by
    apply completedBlock_disjoint
    rw [← blockStart_succ]
    exact blockStart_monotone k hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · have hi : 0 ≤ completedBlockTerm k w i := completedBlock_nonneg (blockStart k i) (k i) (w i) (hw i)
    have hj : 0 ≤ completedBlockTerm k w j := completedBlock_nonneg (blockStart k j) (k j) (w j) (hw j)
    simpa only [star_mul, hi.star_eq, hj.star_eq, star_zero] using congrArg star (hlt j i h)

theorem exists_completedBlockSum (k : ℕ → ℕ) [∀ j, NeZero (k j)]
    (w : (j : ℕ) → MatrixStage A (k j)) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => ‖w j‖)) :
    ∃ b : CornerCompletion A, 0 ≤ b ∧
      Tendsto (fun n => ∑ j ∈ Finset.range n, completedBlockTerm k w j) atTop (𝓝 b) ∧
      ∀ τ : TracialState A, completedRootRank τ b = ∑' j, matrixRank τ (w j) := by
  have hn : Summable (fun j => ‖completedBlockTerm k w j‖) := by
    simpa only [completedBlockTerm, completedBlock_norm] using hs
  have ht : Summable (completedBlockTerm k w) := Summable.of_norm_bounded hn (fun _ => le_rfl)
  have hp (j : ℕ) : 0 ≤ completedBlockTerm k w j := completedBlock_nonneg _ _ _ (hw j)
  refine ⟨∑' j, completedBlockTerm k w j, tsum_nonneg hp, ht.hasSum.tendsto_sum_nat, ?_⟩
  intro τ
  rw [completedRootRank_tsum_orthogonal τ _ hp (completedBlockTerm_orthogonal k w hw) ht]
  congr 1
  funext j
  exact completedBlock_rank τ _ _ _ (hw j)
end CuntzPureness

end

end OAI
