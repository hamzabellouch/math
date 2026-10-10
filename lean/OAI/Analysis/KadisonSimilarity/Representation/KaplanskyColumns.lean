import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyDischarge
import OAI.Analysis.KadisonSimilarity.Derivation.ColumnCompression

namespace OAI

/-! Matrix-column Kaplansky approximation in the original C-star algebra. -/
noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The column approximation input follows from the proved unit-ball
Kaplansky theorem. The constructed column even has norm at most one. -/
theorem kaplanskyColumnApproximation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    KaplanskyColumnApproximation σ := by
  classical
  intro n V hV hentry ζ ε hε
  by_cases hn : n = 0
  · subst n
    refine ⟨0, by simp, ?_⟩
    have he : columnAction σ (0 : Matrix (Fin 0) (Fin 1) A) ζ - V ζ = 0 :=
      Subsingleton.elim _ _
    rw [he, norm_zero]
    exact hε
  let : NeZero n := ⟨hn⟩
  let j : Fin n := 0
  let Q : HilbertCopies H n →L[ℂ] HilbertCopies H n :=
    V.comp (PiLp.proj 2 (fun _ : Fin n => H) j)
  let M : Matrix (Fin n) (Fin n) (H →L[ℂ] H) :=
    Matrix.of (fun i k => if k = j then columnEntry V i else 0)
  have hM : matrixOperator M = Q := by
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    rw [matrixOperator_apply, Finset.sum_eq_single j]
    · simp [M, Q, columnEntry_apply]
    · intro k _ hkj
      simp [M, hkj]
    · simp
  have hQmem : Q ∈ representationVonNeumannAlgebra (representedMatrixHom σ n) := by
    rw [← hM]
    apply (matrixOperator_mem_representationVonNeumannAlgebra_iff σ M).mpr
    intro i k
    dsimp [M]
    split_ifs
    · exact hentry i
    · exact (representationVonNeumannAlgebra σ).zero_mem
  have hQnorm : ‖Q‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro x
    change ‖V (x j)‖ ≤ 1 * ‖x‖
    calc
      ‖V (x j)‖ ≤ ‖V‖ * ‖x j‖ := V.le_opNorm _
      _ ≤ 1 * ‖x j‖ := mul_le_mul_of_nonneg_right hV (norm_nonneg _)
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) zero_le_one
  let w : HilbertCopies H n := PiLp.single 2 j ζ
  obtain ⟨X, hX, happrox⟩ := kaplansky_contraction_approximation
    (representedMatrixHom σ n) Q hQmem hQnorm {w} ε hε
  let W : Matrix (Fin n) (Fin 1) A := Matrix.of (fun i _ => X i j)
  have hW : CStarMatrix.ofMatrix W = cstarColumn X j := rfl
  refine ⟨W, (hW ▸ (norm_cstarColumn_le X j).trans hX).trans (by norm_num), ?_⟩
  have haction : columnAction σ W ζ = representedMatrixHom σ n X w := by
    apply PiLp.ext
    intro i
    rw [columnAction_apply]
    let N : Matrix (Fin n) (Fin n) (H →L[ℂ] H) := Matrix.of (fun i k => σ (X i k))
    change σ (X i j) ζ = matrixEntryCompression i j (matrixOperator N) ζ
    rw [matrixEntryCompression_matrixOperator N]
    rfl
  have hQw : Q w = V ζ := by simp [Q, w]
  rw [haction, ← hQw]
  exact happrox w (Finset.mem_singleton_self w)

end KadisonSimilarity

end

end OAI
