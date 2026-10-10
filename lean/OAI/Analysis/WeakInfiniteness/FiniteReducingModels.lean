import Mathlib
import OAI.Analysis.WeakInfiniteness.FixedColumns
import OAI.Analysis.WeakInfiniteness.OperatorReducing
import OAI.Analysis.WeakInfiniteness.Plateau
import OAI.Analysis.WeakInfiniteness.ReducingColumns

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped InnerProductSpace CStarAlgebra ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma exact_column_reducing_model {n d : ℕ}
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (L : CStarMatrix (Fin n) (Fin d) A)
    (e : A) (hL : L.conjTranspose*L=diagonalCopies d e)
    (ξ : H) (hξ : ‖ξ‖=1) (he : π e ξ=ξ) (D : CStarMatrix (Fin d) (Fin d) ℂ) :
    ∃ J : HilbertVector (Fin d) ℂ →ₗᵢ[ℂ] HilbertVector (Fin n) H,
      (matrixRepresentation π (Fin n) (matrixScalarRight L D*L.conjTranspose)).comp J.toContinuousLinearMap=
        J.toContinuousLinearMap.comp (scalarMatrixAction (H := ℂ) D) ∧
      (matrixRepresentation π (Fin n) (matrixScalarRight L D*L.conjTranspose)).adjoint.comp J.toContinuousLinearMap=
        J.toContinuousLinearMap.comp (scalarMatrixAction (H := ℂ) D).adjoint := by
  let F := rectangularRepresentation π L
  let T := vectorTensorIsometry (n := Fin d) ξ hξ
  let a := scalarMatrixAction (H := H) D
  have hi : F.adjoint.comp (F.comp T.toContinuousLinearMap)=T.toContinuousLinearMap := by
    rw [← ContinuousLinearMap.comp_assoc]
    change ((rectangularRepresentation π L).adjoint.comp (rectangularRepresentation π L)).comp
      T.toContinuousLinearMap = _
    rw [← rectangularRepresentation_star, ← rectangularRepresentation_mul, hL,
      rectangularRepresentation_square]
    exact diagonal_rep_plateau π e ξ hξ he d
  have ha := scalarAction_vectorTensor D ξ hξ
  have ha' : a.adjoint.comp T.toContinuousLinearMap=
      T.toContinuousLinearMap.comp (scalarMatrixAction (H := ℂ) D).adjoint := by
    rw [← scalarMatrixAction_star, ← scalarMatrixAction_star]
    exact scalarAction_vectorTensor D.conjTranspose ξ hξ
  obtain ⟨J,_,hJ,hJ'⟩ := exists_reducing_column F T (scalarMatrixAction (H := ℂ) D) a hi ha ha'
  have hw : matrixRepresentation π (Fin n) (matrixScalarRight L D*L.conjTranspose)=
      F.comp (a.comp F.adjoint) := by
    rw [← rectangularRepresentation_square, rectangularRepresentation_mul,
      rectangularRepresentation_scalarRight, rectangularRepresentation_star,
      ContinuousLinearMap.comp_assoc]
  exact ⟨J, by rwa [hw], by rwa [hw]⟩

lemma representation_plateau_vector (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (c : A) (hc : 0 ≤ c)
    {α : ℝ} (hα : 0 < α) (hαc : α ≤ ‖π c‖) :
    ∃ ξ : H, ‖ξ‖=1 ∧ π (cfcₙ (spectralRamp (α/8)) (positiveCut (α/2) c)) ξ=ξ := by
  have hcπ : 0 ≤ π c := map_nonneg π hc
  obtain ⟨ξ,hξ,he⟩ := exists_plateau_vector hcπ hα hαc
  refine ⟨ξ,hξ,?_⟩
  have hcut : π (positiveCut (α/2) c)=positiveCut (α/2) (π c) :=
    π.map_cfcₙ (fun s : ℝ => max (s-α/2) 0) c (by fun_prop)
      (max_eq_right (by linarith)) (by fun_prop) hc.isSelfAdjoint hcπ.isSelfAdjoint
  rw [π.map_cfcₙ (spectralRamp (α/8)) (positiveCut (α/2) c)
    (continuous_spectralRamp _).continuousOn (spectralRamp_eq_zero (by positivity) (by positivity))
    (by fun_prop) (positiveCut_nonneg _ _).isSelfAdjoint
    ((positiveCut_nonneg (α/2) c).isSelfAdjoint.map π), hcut]
  exact he

theorem exists_uniform_reducing_model {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (c : A) (hc : 0 ≤ c) {α : ℝ} (hα : 0 < α) (d : ℕ)
    (D : CStarMatrix (Fin d) (Fin d) ℂ) (hD : ‖D‖ ≤ 1) :
    ∃ w : CStarMatrix (Fin n) (Fin n) A, ‖w‖ ≤ 1 ∧
      diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)*w*
        diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)=w ∧
      ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), α ≤ ‖π c‖ →
        ∃ J : HilbertVector (Fin d) ℂ →ₗᵢ[ℂ] HilbertVector (Fin n) H,
          (matrixRepresentation π (Fin n) w).comp J.toContinuousLinearMap=
            J.toContinuousLinearMap.comp (scalarMatrixAction (H := ℂ) D) ∧
          (matrixRepresentation π (Fin n) w).adjoint.comp J.toContinuousLinearMap=
            J.toContinuousLinearMap.comp (scalarMatrixAction (H := ℂ) D).adjoint := by
  obtain ⟨L,hL,_,hLn,hEL⟩ := exists_finite_model_columns hn hpi c hα d
  let w := matrixScalarRight L D*L.conjTranspose
  let E := diagonalCopies n (cfcₙ (spectralRamp (α/4)) c)
  have hE : 0 ≤ E := diagonalCopies_nonneg n (cfcₙ_nonneg (fun s _ => spectralRamp_nonneg _ s))
  have hLE : L.conjTranspose*E=L.conjTranspose := by
    have h := congrArg CStarMatrix.conjTranspose hEL
    rw [rectangular_star_mul] at h
    change L.conjTranspose*star E=L.conjTranspose at h
    rwa [hE.star_eq] at h
  refine ⟨w, ?_, ?_, ?_⟩
  · calc
      ‖w‖ ≤ ‖matrixScalarRight L D‖*‖L.conjTranspose‖ := rectangular_norm_mul_le _ _
      _ ≤ (‖L‖*‖D‖)*‖L‖ := by rw [rectangular_norm_conjTranspose]; gcongr; exact matrixScalarRight_norm_le _ _
      _ ≤ (1*1)*1 := by gcongr
      _ = 1 := by norm_num
  · change E*(matrixScalarRight L D*L.conjTranspose)*E=matrixScalarRight L D*L.conjTranspose
    rw [← rectangular_mul_assoc E, matrixScalarRight_mul_left, hEL,
      rectangular_mul_assoc, hLE]
  · intro H _ _ _ π hαc
    obtain ⟨ξ,hξ,he⟩ := representation_plateau_vector π c hc hα hαc
    exact exact_column_reducing_model π L _ hL ξ hξ he D

end

end WeakPureInfiniteness
end

end OAI
