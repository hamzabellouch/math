import OAI.Analysis.KadisonSimilarity.Representation.KaplanskySelfAdjoint
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialSymmetryExtraction

namespace OAI

/-! The two-by-two step from selfadjoint to arbitrary contractions. -/
noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The selfadjoint off-diagonal operator associated to a contraction. -/
def kaplanskyOffDiagonal (T : H →L[ℂ] H) : HilbertCopies H 2 →L[ℂ] HilbertCopies H 2 :=
  representedMatrix (StarAlgHom.id ℂ (H →L[ℂ] H)) (offdiag T (star T))

/-- A matrix-bicommutant membership bridge is the only algebraic fact needed
by the two-by-two contraction argument. -/
theorem kaplansky_contraction_of_offDiagonal_mem
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (hmem : kaplanskyOffDiagonal T ∈
      representationVonNeumannAlgebra (representedMatrixHom σ 2))
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ x ∈ s, ‖σ a x - T x‖ < ε := by
  classical
  have hsa : IsSelfAdjoint (kaplanskyOffDiagonal T) :=
    (offdiag_selfAdjoint T).map (representedMatrixHom (StarAlgHom.id ℂ (H →L[ℂ] H)) 2)
  have hnorm : ‖kaplanskyOffDiagonal T‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le
      (representedMatrixHom (StarAlgHom.id ℂ (H →L[ℂ] H)) 2) _).trans
        (offdiag_norm_le_one T hT)
  let s' : Finset (HilbertCopies H 2) := s.image (PiLp.single 2 (1 : Fin 2))
  obtain ⟨X, -, hX, happrox⟩ := selfAdjoint_kaplansky_approximation
    (representedMatrixHom σ 2) (kaplanskyOffDiagonal T) hmem hsa hnorm s' ε hε
  refine ⟨X 0 1, CStarMatrix.norm_entry_le_norm.trans hX, ?_⟩
  intro x hx
  have happ := happrox (PiLp.single 2 (1 : Fin 2) x)
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hcoordinate := PiLp.norm_apply_le
    (representedMatrixHom σ 2 X (PiLp.single 2 (1 : Fin 2) x) -
      kaplanskyOffDiagonal T (PiLp.single 2 (1 : Fin 2) x)) (0 : Fin 2)
  have he : (representedMatrixHom σ 2 X (PiLp.single 2 (1 : Fin 2) x) -
      kaplanskyOffDiagonal T (PiLp.single 2 (1 : Fin 2) x)) 0 = σ (X 0 1) x - T x := by
    let M₁ : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H) := Matrix.of (fun i j => σ (X i j))
    let M₂ : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H) :=
      Matrix.of (fun i j => (StarAlgHom.id ℂ (H →L[ℂ] H)) (offdiag T (star T) i j))
    change (matrixEntryCompression 0 1 (matrixOperator M₁)) x -
      (matrixEntryCompression 0 1 (matrixOperator M₂)) x = _
    rw [matrixEntryCompression_matrixOperator M₁, matrixEntryCompression_matrixOperator M₂]
    rfl
  rw [he] at hcoordinate
  exact hcoordinate.trans_lt happ

end KadisonSimilarity

end

end OAI
