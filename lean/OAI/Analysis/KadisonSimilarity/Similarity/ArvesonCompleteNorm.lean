import OAI.Analysis.KadisonSimilarity.Similarity.ArvesonLowerBound
import OAI.Analysis.KadisonSimilarity.Similarity.SharpCompletelyBoundedDerivation

namespace OAI

/-! The concrete completely bounded commutator norm controls the actual
entrywise C-star matrix amplifications needed for factorization. -/

noncomputable section
namespace KadisonSimilarity
open scoped ENNReal ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem entrywise_bound_of_unit_ball (T : A →ₗ[ℂ] (H →L[ℂ] H)) {C : ℝ}
    (hunit : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X‖ ≤ 1 → ‖X.map T‖ ≤ C)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) : ‖X.map T‖ ≤ C * ‖X‖ := by
  by_cases hx : X = 0
  · subst X
    have hz : CStarMatrix.map (0 : CStarMatrix (Fin n) (Fin n) A) T = 0 := by
      apply CStarMatrix.ext
      intro i j
      exact T.map_zero
    simp only [hz, norm_zero, mul_zero, le_refl]
  have hr : 0 < ‖X‖ := norm_pos_iff.mpr hx
  let c : ℂ := (‖X‖ : ℂ)⁻¹
  have hc : ‖c‖ = ‖X‖⁻¹ := by
    simp only [c, norm_inv, Complex.norm_real, norm_norm]
  have hy : ‖c • X‖ ≤ 1 := by
    rw [norm_smul, hc, inv_mul_cancel₀ hr.ne']
  have he : (c • X).map T = c • X.map T := by
    apply CStarMatrix.ext
    intro i j
    exact T.map_smul c (X i j)
  have hb := hunit n (c • X) hy
  rw [he, norm_smul, hc] at hb
  calc
    ‖X.map T‖ = ‖X‖ * (‖X‖⁻¹ * ‖X.map T‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    _ ≤ ‖X‖ * C := mul_le_mul_of_nonneg_left hb hr.le
    _ = C * ‖X‖ := mul_comm _ _

local instance arvesonComplete_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

def commutantDerivation (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    M.commutant.toStarSubalgebra →L[ℂ] (H →L[ℂ] H) :=
  (innerDerivation T).comp M.commutant.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL

theorem commutantDerivation_leibniz (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (a b : M.commutant.toStarSubalgebra) :
    commutantDerivation M T (a * b) =
      (a : H →L[ℂ] H).comp (commutantDerivation M T b) +
      (commutantDerivation M T a).comp (b : H →L[ℂ] H) := by
  change T * ((a : H →L[ℂ] H) * (b : H →L[ℂ] H)) -
    ((a : H →L[ℂ] H) * (b : H →L[ℂ] H)) * T =
      (a : H →L[ℂ] H) * (T * (b : H →L[ℂ] H) - (b : H →L[ℂ] H) * T) +
      (T * (a : H →L[ℂ] H) - (a : H →L[ℂ] H) * T) * (b : H →L[ℂ] H)
  noncomm_ring

theorem commutantDerivation_complete_bound (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hb : completeCommutatorNorm M.commutant T ≤ ENNReal.ofReal C)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) M.commutant.toStarSubalgebra) :
    ‖X.map (commutantDerivation M T).toLinearMap‖ ≤ C * ‖X‖ := by
  apply entrywise_bound_of_unit_ball
  intro m Y hY
  let Z : Matrix (Fin m) (Fin m) (H →L[ℂ] H) := fun i j => (Y i j : H →L[ℂ] H)
  have hZ : ‖matrixOperator Z‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le
      (representedMatrixHom M.commutant.toStarSubalgebra.subtype m) Y).trans hY
  have hsup : ENNReal.ofReal ‖commutator (amplify T m) (matrixOperator Z)‖ ≤
      completeCommutatorNorm M.commutant T := by
    exact le_iSup_of_le m (le_iSup_of_le Z
      (le_iSup_of_le (fun i j => (Y i j).property) (le_iSup_of_le hZ le_rfl)))
  have hn := (ENNReal.ofReal_le_ofReal_iff hC).mp (hsup.trans hb)
  rw [← norm_matrixOperator_eq m]
  have he : matrixOperator
      (CStarMatrix.ofMatrix.symm (Y.map (commutantDerivation M T).toLinearMap)) =
      commutator (amplify T m) (matrixOperator Z) := by
    rw [commutator_amplify_matrixOperator]
    rfl
  rw [he]
  exact hn

end KadisonSimilarity

end

end OAI
