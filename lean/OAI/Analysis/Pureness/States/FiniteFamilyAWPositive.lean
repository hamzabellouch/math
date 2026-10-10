import OAI.Analysis.Pureness.States.FiniteFamilyUltraproduct
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientIteration
import OAI.Analysis.Pureness.Cuntz.FinOneMatrixTransport

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace
open scoped NNReal ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
variable (hF : F.level 1 1=1) (U : Ultrafilter ℕ)

instance matrixUltraAWNontrivial : Nontrivial (F.MatrixUltraAW hmono hF U) := by
  apply nontrivial_of_ne (1 : F.MatrixUltraAW hmono hF U) 0
  intro h
  have he := congrArg (F.matrixUltraQuasitrace hmono hF U).toFun h
  rw [F.matrixUltraQuasitrace_unit,(F.matrixUltraQuasitrace hmono hF U).map_zero] at he
  exact one_ne_zero he

abbrev matrixUltralimitPositive :=
  ultralimitPositiveQuasitrace (F.normalizedPositiveLevel hmono) U (F.normalizedPositiveLevel_unit hmono hF)

abbrev matrixUltralimitTriangle :=
  ultralimitPositiveQuasitrace_metricSize_add (F.normalizedPositiveLevel hmono) U
    (F.normalizedPositiveLevel_unit hmono hF) (F.normalizedPositiveLevel_metricSize_add hmono)

abbrev matrixUltralimitSqrt :=
  ultralimitPositiveQuasitrace_sqrt_add (F.normalizedPositiveLevel hmono) U
    (F.normalizedPositiveLevel_unit hmono hF) (F.normalizedPositiveLevel_sqrt_add hmono)

abbrev matrixAWPositive :=
  (F.matrixUltralimitPositive hmono hF U).quotientPositiveQuasitrace
    (F.matrixUltralimitTriangle hmono hF U) (F.matrixUltralimitSqrt hmono hF U)

lemma matrixAWPositive_complex (x : F.MatrixUltraAW hmono hF U) :
    (F.matrixAWPositive hmono hF U).complexValue x=F.matrixUltraQuasitrace hmono hF U x := rfl

abbrev matrixAWPositive_triangle :=
  (F.matrixUltralimitPositive hmono hF U).quotientPositiveQuasitrace_metricSize_add
    (F.matrixUltralimitTriangle hmono hF U) (F.matrixUltralimitSqrt hmono hF U)

abbrev matrixAWPositive_sqrt :=
  (F.matrixUltralimitPositive hmono hF U).quotientPositiveQuasitrace_sqrt_add
    (F.matrixUltralimitTriangle hmono hF U) (F.matrixUltralimitSqrt hmono hF U)

def matrixFinOneAW : FinMatrix A 1 →⋆ₐ[ℂ] F.MatrixUltraAW hmono hF U :=
  (F.matrixDiagonalAWMap hmono hF U).comp scalarFinOneEquiv.symm.toStarAlgHom

lemma matrixFinOneAW_complex (M : FinMatrix A 1) :
    (F.matrixAWPositive hmono hF U).complexValue (F.matrixFinOneAW hmono hF U M)=
      (F.positiveLevel hmono 1).complexValue M := by
  rw [F.matrixAWPositive_complex]
  change F.matrixUltraQuasitrace hmono hF U (F.matrixDiagonalAWMap hmono hF U (scalarFinOneEquiv.symm M))=_
  rw [F.matrixDiagonalAWMap_value]
  change F.level 1 (scalarFinOneEquiv (scalarFinOneEquiv.symm M))=_
  rw [StarAlgEquiv.apply_symm_apply]
  exact ((F.level 1).toPositiveQuasitrace_complexValue (hmono 1) M).symm

lemma matrixFinOneAW_positive (M : Positive (FinMatrix A 1)) :
    F.matrixAWPositive hmono hF U (Positive.map (F.matrixFinOneAW hmono hF U).toNonUnitalStarAlgHom M)=
      (1 : ℝ)*F.positiveLevel hmono 1 M := by
  have h := F.matrixFinOneAW_complex hmono hF U M.1
  have he := (F.matrixAWPositive hmono hF U).complexValue_positive
    (Positive.map (F.matrixFinOneAW hmono hF U).toNonUnitalStarAlgHom M)
  change (F.matrixAWPositive hmono hF U).complexValue (F.matrixFinOneAW hmono hF U M.1)=_ at he
  rw [he,(F.positiveLevel hmono 1).complexValue_positive M] at h
  rw [one_mul]
  exact Complex.ofReal_injective h
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
