import OAI.Analysis.Pureness.States.FiniteFamilyNormalizedMatrices
import OAI.Analysis.Pureness.States.NormalizedMatrixStateDiagonal
import OAI.Analysis.Pureness.Projections.UltralimitAWNormality

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace Filter
open scoped NNReal ENNReal Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
variable (hF : F.level 1 1=1) (U : Ultrafilter ℕ)

abbrev MatrixUltraAW := UltralimitAWCompletion (F.normalizedPositiveLevel hmono) U
  (F.normalizedPositiveLevel_unit hmono hF) (F.normalizedPositiveLevel_metricSize_add hmono)

def matrixUltraQuasitrace : ComplexQuasitrace (F.MatrixUltraAW hmono hF U) :=
  ultralimitAWQuasitrace (F.normalizedPositiveLevel hmono) U
    (F.normalizedPositiveLevel_unit hmono hF) (F.normalizedPositiveLevel_metricSize_add hmono)
    (F.normalizedPositiveLevel_sqrt_add hmono)

lemma matrixUltraQuasitrace_unit : F.matrixUltraQuasitrace hmono hF U 1=1 :=
  ultralimitAWQuasitrace_unit _ _ _ _ _

lemma matrixUltraQuasitrace_faithful (x : F.MatrixUltraAW hmono hF U) :
    F.matrixUltraQuasitrace hmono hF U (star x*x)=0 ↔ x=0 :=
  ultralimitAWQuasitrace_faithful _ _ _ _ _ x

theorem matrixUltraAW_finite (x : F.MatrixUltraAW hmono hF U) (hx : star x*x=1) : x*star x=1 :=
  ultralimitAWCompletion_finite _ _ _ _ (F.normalizedPositiveLevel_sqrt_add hmono) x hx

theorem matrixUltraAW_annihilator (S : Set (F.MatrixUltraAW hmono hF U)) :
    ∃ p : F.MatrixUltraAW hmono hF U, IsStarProjection p ∧ ∀ z, (∀ a ∈ S, a*z=0) ↔ p*z=z :=
  ultralimitAWCompletion_annihilator _ _ _ _ (F.normalizedPositiveLevel_sqrt_add hmono) S

lemma matrixUltraPositive_diagonal (a : Positive A) :
    ultralimitPositiveQuasitrace (F.normalizedPositiveLevel hmono) U
      (F.normalizedPositiveLevel_unit hmono hF)
      (Positive.map (matrixStateDiagonalProduct (A := A)).toNonUnitalStarAlgHom a)=
        F.positiveLevel hmono 1 (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) := by
  apply tendsto_nhds_unique (quasitraceUltraPositive_tendsto
    (F.normalizedPositiveLevel hmono) U (F.normalizedPositiveLevel_unit hmono hF)
    (Positive.map (matrixStateDiagonalProduct (A := A)).toNonUnitalStarAlgHom a))
  have he (n : ℕ) : F.normalizedPositiveLevel hmono n
      (boundedProductPositiveEval n (Positive.map (matrixStateDiagonalProduct (A := A)).toNonUnitalStarAlgHom a))=
        F.positiveLevel hmono 1 (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) :=
    F.normalizedPositiveLevel_scalar hmono n a
  simp only [he]
  exact tendsto_const_nhds

def matrixDiagonalAWMap : A →⋆ₐ[ℂ] F.MatrixUltraAW hmono hF U :=
  (ultralimitCompletionMap (F.normalizedPositiveLevel hmono) U
    (F.normalizedPositiveLevel_unit hmono hF) (F.normalizedPositiveLevel_metricSize_add hmono)).comp
      matrixStateDiagonalProduct

lemma matrixDiagonalAWMap_value (x : A) :
    F.matrixUltraQuasitrace hmono hF U (F.matrixDiagonalAWMap hmono hF U x)=F.toTwoQuasitrace.base x := by
  dsimp only [matrixDiagonalAWMap,StarAlgHom.comp_apply,matrixUltraQuasitrace]
  rw [ultralimitAWQuasitrace_original]
  let P := (F.positiveLevel hmono 1).comap (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom
  have h := PositiveQuasitrace.complexValue_map
    (ultralimitPositiveQuasitrace (F.normalizedPositiveLevel hmono) U (F.normalizedPositiveLevel_unit hmono hF)) P
    (matrixStateDiagonalProduct (A := A)).toNonUnitalStarAlgHom (F.matrixUltraPositive_diagonal hmono hF U) x
  have hP : P.complexValue x=F.toTwoQuasitrace.base x :=
    ((F.positiveLevel hmono 1).comap_complexValue
      (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom x).trans
      ((F.level 1).toPositiveQuasitrace_complexValue (hmono 1) (scalarMatrixHom x))
  exact h.trans hP
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
