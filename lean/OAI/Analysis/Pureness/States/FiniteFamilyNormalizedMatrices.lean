import OAI.Analysis.Pureness.States.FiniteFamilyBaseCarrier
import OAI.Analysis.Pureness.Quasitrace.PositiveQuasitraceScaling
import OAI.Analysis.Pureness.States.ScalarMatrixEmbedding

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace
open scoped NNReal CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))

def normalizedPositiveLevel (n : ℕ) : PositiveQuasitrace (FinMatrix A (n+1)) :=
  (F.positiveLevel hmono (n+1)).scale ⟨(n+1 : ℝ)⁻¹,by positivity⟩

lemma normalizedPositiveLevel_unit (hF : F.level 1 1=1) (n : ℕ) :
    F.normalizedPositiveLevel hmono n ⟨1,zero_le_one⟩=1 := by
  change (n+1 : ℝ)⁻¹*F.positiveLevel hmono (n+1) ⟨1,zero_le_one⟩=1
  rw [F.positiveLevel_unit hmono hF]
  push_cast
  exact inv_mul_cancel₀ (by positivity)

lemma normalizedPositiveLevel_metricSize_add (n : ℕ) (x y : FinMatrix A (n+1)) :
    (F.normalizedPositiveLevel hmono n).metricSize (x+y) ≤
      (F.normalizedPositiveLevel hmono n).metricSize x+(F.normalizedPositiveLevel hmono n).metricSize y :=
  PositiveQuasitrace.scale_metricSize_add _ _ (F.positiveLevel_metricSize_add hmono (n+1)) x y

lemma normalizedPositiveLevel_sqrt_add (n : ℕ) (a b : Positive (FinMatrix A (n+1))) :
    Real.sqrt (F.normalizedPositiveLevel hmono n (Positive.add a b)) ≤
      Real.sqrt (F.normalizedPositiveLevel hmono n a)+Real.sqrt (F.normalizedPositiveLevel hmono n b) :=
  PositiveQuasitrace.scale_sqrt_add _ _ (F.positiveLevel_sqrt_add hmono (n+1)) a b

lemma normalizedPositiveLevel_scalar (n : ℕ) (a : Positive A) :
    F.normalizedPositiveLevel hmono n (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a)=
      F.positiveLevel hmono 1 (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) := by
  change (n+1 : ℝ)⁻¹*F.positiveLevel hmono (n+1) (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a)=_
  rw [F.positiveLevel_scalarMatrix,← mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]

lemma normalizedPositiveLevel_scalar_complex (n : ℕ) (x : A) :
    (F.normalizedPositiveLevel hmono n).complexValue (scalarMatrixHom (ι := Fin (n+1)) x)=
      F.toTwoQuasitrace.base x := by
  let P := (F.positiveLevel hmono 1).comap (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom
  have h := PositiveQuasitrace.complexValue_map (F.normalizedPositiveLevel hmono n) P
    (scalarMatrixHom (ι := Fin (n+1))).toNonUnitalStarAlgHom (F.normalizedPositiveLevel_scalar hmono n) x
  change (F.normalizedPositiveLevel hmono n).complexValue (scalarMatrixHom (ι := Fin (n+1)) x)=P.complexValue x at h
  rw [h]
  change ((F.positiveLevel hmono 1).comap _).complexValue x=_
  rw [PositiveQuasitrace.comap_complexValue]
  exact (F.level 1).toPositiveQuasitrace_complexValue (hmono 1) (scalarMatrixHom x)

lemma normalizedPositiveLevel_scalarCoefficient (hF : F.level 1 1=1)
    (n : ℕ) (z : FinMatrix ℂ (n+1)) :
    (F.normalizedPositiveLevel hmono n).complexValue (scalarCoefficientMatrixHom z)=
      (n+1 : ℂ)⁻¹*Matrix.trace (CStarMatrix.ofMatrix.symm z) := by
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    positiveQuasitrace_scalarCoefficientMatrix (F.normalizedPositiveLevel hmono n) (0 : Fin (n+1))
      (F.normalizedPositiveLevel_unit hmono hF n) z
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
