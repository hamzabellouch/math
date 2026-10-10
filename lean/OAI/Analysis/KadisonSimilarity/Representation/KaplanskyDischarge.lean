import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyGeneral
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixVonNeumannRange
import OAI.Analysis.KadisonSimilarity.Representation.ScalarKaplansky

namespace OAI

/-! Finite-vector Kaplansky density with an exact source norm bound. -/
noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Ordered
variable [PartialOrder A] [StarOrderedRing A]

/-- Off-diagonal selfadjoint dilation preserves membership in the matrix
bicommutant of the original representation. -/
theorem kaplanskyOffDiagonal_mem (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) :
    kaplanskyOffDiagonal T ∈ representationVonNeumannAlgebra (representedMatrixHom σ 2) := by
  let M : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H) :=
    Matrix.of (fun i j => (StarAlgHom.id ℂ (H →L[ℂ] H)) (offdiag T (star T) i j))
  change matrixOperator M ∈ _
  apply (matrixOperator_mem_representationVonNeumannAlgebra_iff σ M).mpr
  intro i j
  fin_cases i <;> fin_cases j
  · exact (representationVonNeumannAlgebra σ).zero_mem
  · exact hT
  · exact star_mem hT
  · exact (representationVonNeumannAlgebra σ).zero_mem

/-- The unit ball of the source algebra is strongly dense in the unit ball
of the represented bicommutant, tested on any finite family of vectors. -/
theorem kaplansky_contraction_approximation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ) (hn : ‖T‖ ≤ 1)
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ x ∈ s, ‖σ a x - T x‖ < ε :=
  kaplansky_contraction_of_offDiagonal_mem σ T hn (kaplanskyOffDiagonal_mem σ T hT) s ε hε

/-- Scaling the unit-ball statement retains the exact norm of the target. -/
theorem kaplansky_finite_approximation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, ‖a‖ ≤ ‖T‖ ∧ ∀ x ∈ s, ‖σ a x - T x‖ < ε := by
  by_cases hzero : T = 0
  · subst T
    refine ⟨0, by simp, ?_⟩
    intro x _
    simpa using hε
  let d : ℝ := ‖T‖
  have hd : 0 < d := norm_pos_iff.mpr hzero
  let D : H →L[ℂ] H := d⁻¹ • T
  have hD : D ∈ representationVonNeumannAlgebra σ := by
    change d⁻¹ • T ∈ _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact (representationVonNeumannAlgebra σ).toStarSubalgebra.smul_mem hT _
  have hDn : ‖D‖ ≤ 1 := by
    rw [show D = d⁻¹ • T from rfl, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd]
    change d⁻¹ * d ≤ 1
    rw [inv_mul_cancel₀ (ne_of_gt hd)]
  obtain ⟨a, ha, happrox⟩ := kaplansky_contraction_approximation σ D hD hDn s
    (ε / d) (div_pos hε hd)
  refine ⟨d • a, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg hd.le]
    exact (mul_le_mul_of_nonneg_left ha hd.le).trans_eq (mul_one d)
  · intro x hx
    have hscale : σ (d • a) = d • σ a := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
      rfl
    have hrecover : d • D = T := by
      dsimp [D]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hd), one_smul]
    have hTx : T x = d • D x := congrArg (fun R : H →L[ℂ] H => R x) hrecover.symm
    rw [hscale, smul_apply, hTx, ← smul_sub, norm_smul, Real.norm_of_nonneg hd.le]
    calc
      d * ‖σ a x - D x‖ < d * (ε / d) := mul_lt_mul_of_pos_left (happrox x hx) hd
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hd)

end Ordered

/-- Two-vector Kaplansky approximation, using the canonical spectral order
on the matrix C-star algebra. -/
theorem twoVectorKaplanskyInput (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    TwoVectorKaplanskyInput σ (representationVonNeumannAlgebra σ) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  classical
  intro T hT x y ε hε
  obtain ⟨a, ha, happrox⟩ := kaplansky_finite_approximation σ T hT {x, y} ε hε
  exact ⟨a, ha.trans (le_add_of_nonneg_right hε.le),
    (happrox x (by simp)).le, (happrox y (by simp)).le⟩

end KadisonSimilarity

end

end OAI
