import OAI.Analysis.Pureness.Quasitrace.QuasitracePullback

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def firstMatrixCorner : A →⋆ₙₐ[ℂ] FinMatrix A 2 :=
  (matrixInclusion (show 1 ≤ 2 from by decide)).comp
    (scalarMatrixHom (ι := Fin 1) (A := A)).toNonUnitalStarAlgHom

omit [PartialOrder A] [StarOrderedRing A] in
lemma firstMatrixCorner_eq_single (x : A) :
    firstMatrixCorner x = singleMatrix (0 : Fin 2) 0 x := by
  change matrixPad (show 1 ≤ 2 from by decide) (scalarMatrixHom (ι := Fin 1) x) = _
  rw [matrixPad_succ (Nat.le_refl 1),matrixPad_self]
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixSuccessor,scalarMatrixHom,diagonalMatrixHom,singleMatrix]
  all_goals rfl

structure TwoQuasitrace (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  base : ComplexQuasitrace A
  matrix : ComplexQuasitrace (FinMatrix A 2)
  extension : ∀ x : A, base x = matrix (firstMatrixCorner x)

def finiteSpectralTwoQuasitrace
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) : TwoQuasitrace A where
  base := ((finiteSpectralPositiveQuasitrace d hd hlsc hfinite 1).comap
    (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom).toComplex
  matrix := (finiteSpectralQuasitraceFamily d hd hlsc hfinite).level 2
  extension x := by
    change ((finiteSpectralPositiveQuasitrace d hd hlsc hfinite 1).comap
      (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom).complexValue x =
      (finiteSpectralPositiveQuasitrace d hd hlsc hfinite 2).complexValue (firstMatrixCorner x)
    rw [PositiveQuasitrace.comap_complexValue]
    exact ((finiteSpectralQuasitraceFamily d hd hlsc hfinite).inclusion
      (show 1 ≤ 2 from by decide) (scalarMatrixHom (ι := Fin 1) x)).symm

lemma finiteSpectralTwoQuasitrace_unit
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) :
    (finiteSpectralTwoQuasitrace d hd hlsc hfinite).base 1 =
      ((d (finitePositiveClass 1 ⟨1,zero_le_one⟩)).toReal : ℂ) := by
  change ((finiteSpectralPositiveQuasitrace d hd hlsc hfinite 1).comap
    (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom).complexValue 1 = _
  rw [PositiveQuasitrace.comap_complexValue]
  change (finiteSpectralPositiveQuasitrace d hd hlsc hfinite 1).complexValue
    (scalarMatrixHom (ι := Fin 1) 1) = _
  rw [map_one]
  have h := (finiteSpectralPositiveQuasitrace d hd hlsc hfinite 1).complexValue_positive ⟨1,zero_le_one⟩
  change (finiteSpectralPositiveQuasitrace d hd hlsc hfinite 1).complexValue 1 =
    ((finiteSpectralIntegral d 1 ⟨1,zero_le_one⟩).toReal : ℂ) at h
  rw [h,finiteSpectralIntegral_projection d 1 ⟨1,zero_le_one⟩ (by simp [IsIdempotentElem])]
end CuntzPureness

end

end OAI
