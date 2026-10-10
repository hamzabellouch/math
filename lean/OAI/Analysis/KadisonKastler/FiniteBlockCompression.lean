import OAI.Analysis.KadisonKastler.FiniteBlockExtension

namespace OAI

/-! # Contractive finite compressions of the countable amplification -/

namespace KadisonKastler

open Filter
open scoped BigOperators CStarAlgebra Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

local instance compressionOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance compressionOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

def finiteCompression (n : ℕ) (T : H →L[ℂ] H) :
    CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E) := fun i j => F.matrixEntry T i j

theorem blockElement_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) :
    F.blockElement i j (F.matrixEntry T i j) = F.entry i i * T * F.entry j j := by
  rw [blockElement, F.extension_matrixEntry]
  calc
    _ = (F.entry i 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 j) := by
      noncomm_ring
    _ = _ := by rw [F.mul_entry, F.mul_entry]; simp

theorem finiteBlock_compression (n : ℕ) (T : H →L[ℂ] H) :
    F.finiteBlock (F.finiteCompression n T) =
      F.partialDiagonal (Finset.range n) * T * F.partialDiagonal (Finset.range n) := by
  have hd : (∑ i : Fin n, F.entry i i) = F.partialDiagonal (Finset.range n) :=
    Fin.sum_univ_eq_sum_range (fun i => F.entry i i) n
  simp only [finiteBlock, finiteCompression, F.blockElement_matrixEntry]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hd]

theorem norm_finiteCompression_le (n : ℕ) (T : H →L[ℂ] H) :
    ‖F.finiteCompression n T‖ ≤ ‖T‖ := by
  rw [← F.norm_finiteBlock, F.finiteBlock_compression]
  calc
    _ ≤ (‖F.partialDiagonal (Finset.range n)‖ * ‖T‖) *
        ‖F.partialDiagonal (Finset.range n)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖T‖) * 1 := by
      gcongr <;> exact F.norm_partialDiagonal_le _
    _ = ‖T‖ := by ring

theorem blockElement_mem_amplifiedAlgebra (M : VonNeumannAlgebra E)
    (i j : ℕ) {T : E →L[ℂ] E} (hT : T ∈ M) :
    F.blockElement i j T ∈ F.amplifiedAlgebra M := by
  rw [F.mem_amplifiedAlgebra_iff]
  intro k l
  rw [F.matrixEntry_blockElement]
  split_ifs
  · exact hT
  · exact M.zero_mem

theorem finiteBlock_mem_amplifiedAlgebra (M : VonNeumannAlgebra E) {n : ℕ}
    (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) (hX : ∀ i j, X i j ∈ M) :
    F.finiteBlock X ∈ F.amplifiedAlgebra M := by
  apply (F.amplifiedAlgebra M).sum_mem
  intro i _
  apply (F.amplifiedAlgebra M).sum_mem
  intro j _
  exact F.blockElement_mem_amplifiedAlgebra M i j (hX i j)

theorem finiteBlock_compression_tendsto (T : H →L[ℂ] H) (x y : H) :
    Tendsto (fun n => inner ℂ y (F.finiteBlock (F.finiteCompression n T) x))
      atTop (𝓝 (inner ℂ y (T x))) := by
  have ht (z : H) := (F.partialDiagonal_tendsto z).comp tendsto_finset_range
  have hi := (ht y).inner (𝕜 := ℂ) (T.continuous.continuousAt.tendsto.comp (ht x))
  apply hi.congr
  intro n
  rw [F.finiteBlock_compression, mul_apply_eq_comp, mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_left (F.partialDiagonal (Finset.range n))
    (T (F.partialDiagonal (Finset.range n) x)) y]
  simp only [← ContinuousLinearMap.star_eq_adjoint, F.partialDiagonal_star]
  rfl

end FullMatrixCorner

end

end KadisonKastler

end OAI
