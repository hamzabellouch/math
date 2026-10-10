import OAI.Analysis.Pureness.States.ScalarMatrixEmbedding
import OAI.Analysis.Pureness.States.NormalizedMatrixStateDiagonal

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

theorem normalizedMatrixState_scalarCoefficient (n : ℕ) (z : FinMatrix ℂ (n+1)) :
    (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n).complexValue
      (scalarCoefficientMatrixHom z) =
        (n+1 : ℂ)⁻¹ * Matrix.trace (CStarMatrix.ofMatrix.symm z) := by
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    positiveQuasitrace_scalarCoefficientMatrix
      (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n) (0 : Fin (n+1))
      (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f n) z

def scalarCoefficientProductHom :
    lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞ →⋆ₐ[ℂ] lp (fun n : ℕ => FinMatrix A (n+1)) ∞ where
  toFun u := ⟨fun n => scalarCoefficientMatrixHom (u n),memℓp_infty ⟨‖u‖,by
    rintro _ ⟨n,rfl⟩
    exact (NonUnitalStarAlgHom.norm_apply_le (scalarCoefficientMatrixHom (A := A) (ι := Fin (n+1))).toNonUnitalStarAlgHom (u n)).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero u n)⟩⟩
  map_zero' := by apply lp.ext; funext n; exact map_zero scalarCoefficientMatrixHom
  map_one' := by apply lp.ext; funext n; exact map_one scalarCoefficientMatrixHom
  map_add' u v := by apply lp.ext; funext n; exact map_add scalarCoefficientMatrixHom _ _
  map_mul' u v := by apply lp.ext; funext n; exact map_mul scalarCoefficientMatrixHom _ _
  map_star' u := by apply lp.ext; funext n; exact map_star scalarCoefficientMatrixHom _
  commutes' z := by apply lp.ext; funext n; exact scalarCoefficientMatrixHom.commutes z

lemma scalarCoefficientProductHom_commute (x : A) (u : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) :
    Commute (matrixStateDiagonalProduct x) (scalarCoefficientProductHom u) := by
  apply lp.ext
  funext n
  exact scalarCoefficientMatrixHom_commute x (u n)

variable (U : Ultrafilter ℕ)

def scalarCoefficientAWMap :
    lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞ →⋆ₐ[ℂ] NormalizedMatrixStateUltraAW hsimple y hy f U :=
  (ultralimitCompletionMap (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)).comp scalarCoefficientProductHom

lemma scalarCoefficientAWMap_commute (x : A) (u : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) :
    Commute (matrixStateDiagonalAWEmbedding hsimple y hy f U x)
      (scalarCoefficientAWMap hsimple y hy f U u) := by
  let φ := ultralimitCompletionMap (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
  change φ (matrixStateDiagonalProduct x)*φ (scalarCoefficientProductHom u) =
    φ (scalarCoefficientProductHom u)*φ (matrixStateDiagonalProduct x)
  exact (map_mul φ _ _).symm.trans
    ((congrArg φ (scalarCoefficientProductHom_commute (A := A) x u).eq).trans (map_mul φ _ _))
end CuntzPureness

end

end OAI
