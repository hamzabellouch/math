import OAI.Analysis.Kaplansky.MatrixImage
import OAI.Analysis.Kaplansky.MatrixTest

namespace OAI

/-! The polynomial test excluding proper infiniteness of the actual algebra. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem properlyInfinite_actual_polynomial_bound {m : ℕ} (hm : 0<m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ p : Fin m → Fin (m+m) → StarWordPolynomial 24,
      ∀ (y : SmoothTestBase m (matrixPolynomialDegree p))
        (v : MatrixTowerHilbert (testSequenceStage m (matrixPolynomialDegree p)) (m+m) y),
        (1/2 : ℝ)*‖v‖ ≤ ‖matrixPolynomialAction
          (testSequenceStep (R := matrixPolynomialDegree p) hm) Finset.univ
          (matrixPolynomialTerm p) y v‖ := by
  obtain ⟨s,t,hs,ht,hst⟩ := hpi
  let W := properIsometryColumns s t
  let δ : ℝ := 1/(4*((m : ℝ)*(m+m)+1))
  have hd : 0 < 4*((m : ℝ)*(m+m)+1) := by positivity
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨p,hp⟩ := generated_matrix_polynomial_approximation actualBoundedGenerator W hδ
  refine ⟨p,?_⟩
  intro y v
  let z : ActualTestIndex := ⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩
  let P : CStarMatrix (Fin m) (Fin (m+m)) ActualAlgebra :=
    CStarMatrix.ofMatrix (fun i j => generatedWordPolynomial actualBoundedGenerator (p i j))
  let Wz := fun i j => actualRepresentation z (W i j)
  let Pz := fun i j => actualRepresentation z (P i j)
  have hW : ∀ v : HilbertColumns (m+m) (ActualHilbert z), ‖operatorMatrixAction Wz v‖=‖v‖ :=
    operatorMatrixAction_norm Wz
      (actualRepresentation_matrix_column W (properIsometryColumns_column s t hs ht hst) z)
  have hb := operatorMatrix_perturbation_lower_bound Pz Wz hW hδ.le
    (actualRepresentation_matrix_entry_close P W hp z) v
  have hfactor : (1/2 : ℝ) ≤ 1-(m : ℝ)*(m+m)*δ := by
    have he : δ*(4*((m : ℝ)*(m+m)+1))=1 := by
      dsimp [δ]
      field_simp
    have hnonneg : 0 ≤ (m : ℝ)*(m+m) := by positivity
    nlinarith
  simp only [Nat.cast_add] at hb
  have h := (mul_le_mul_of_nonneg_right hfactor (norm_nonneg v)).trans hb
  change (1/2 : ℝ)*‖v‖ ≤ ‖operatorMatrixAction
    (fun i j => actualRepresentation z (generatedWordPolynomial actualBoundedGenerator (p i j))) v‖ at h
  rw [actualPolynomialMatrix_action hm p y v] at h
  exact h

theorem properlyInfinite_actual_image {m : ℕ} (hm : 0<m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ p : Fin m → Fin (m+m) → StarWordPolynomial 24,
      Nonempty (SmoothTestBase m (matrixPolynomialDegree p) × EuclideanSpace ℂ
        (Fin (Fintype.card (towerInputStage (testSequenceStage m (matrixPolynomialDegree p)) (m+m)).Slot)) ≃ₜ
        {z : Bundle.TotalSpace (EuclideanSpace ℂ (RetainedSlot m (matrixPolynomialDegree p)))
          (RetainedBundle m (matrixPolynomialDegree p)) //
          z.2 ∈ LinearMap.range (actualMatrixRestriction hm Finset.univ (matrixPolynomialTerm p) z.proj)}) ∧
      ∀ y : SmoothTestBase m (matrixPolynomialDegree p),
        Module.finrank ℂ (LinearMap.range (actualMatrixRestriction hm Finset.univ (matrixPolynomialTerm p) y)) =
          2*m*testRank m (matrixPolynomialDegree p) 0 := by
  obtain ⟨p,hp⟩ := properlyInfinite_actual_polynomial_bound hm hpi
  refine ⟨p,⟨actualMatrixImageHomeomorph hm Finset.univ (matrixPolynomialTerm p)
    (by norm_num : (0 : ℝ)<1/2) hp⟩,?_⟩
  intro y
  rw [actualMatrixImage_finrank hm Finset.univ (matrixPolynomialTerm p) (by norm_num : (0 : ℝ)<1/2) hp y]
  ring

theorem properlyInfinite_retained_frame {m : ℕ} (hm : 0<m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ R : ℕ, 0<R ∧ Nonempty (ContinuousOrthonormalStageFrame (retainedLineStage m R)
      (2*m*testRank m R 0)) := by
  obtain ⟨p,hp⟩ := properlyInfinite_actual_polynomial_bound hm hpi
  let R := matrixPolynomialDegree p
  let y₀ := testBaseProjectiveHomeomorph m R (bundleTestBasePoint m R)
  let L := actualMatrixStageMap hm Finset.univ (matrixPolynomialTerm p)
  have hi : ∀ y, Function.Injective (L.map y) := fun y =>
    norm_lower_bound_injective _ (by norm_num : (0 : ℝ)<1/2)
      (actualMatrixRestriction_lower_bound hm Finset.univ (matrixPolynomialTerm p) y (1/2) (hp y))
  let f := (trivialMapFrame L (actualInput_label_none m (m+m) R) y₀ hi).normalize
  have hc : Fintype.card (towerInputStage (testSequenceStage m R) (m+m)).Slot =
      2*m*testRank m R 0 := by
    have hr := actualInput_finrank m (m+m) R y₀
    change Module.finrank ℂ (EuclideanSpace ℂ (towerInputStage (testSequenceStage m R) (m+m)).Slot)=_ at hr
    rw [finrank_euclideanSpace] at hr
    rw [hr]
    ring
  refine ⟨R,matrixPolynomialDegree_pos p,?_⟩
  rw [← hc]
  exact ⟨f⟩

end Kaplansky

end

end OAI
