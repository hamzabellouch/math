import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.HilbertFactorization
import OAI.Analysis.TracialCohomology.NormalPreservation

namespace OAI

/-! Normal reduction for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild
open HochschildNormalPart
universe u v

theorem analyticProducer_proved : AnalyticProducerGoal.{u} := by
  intro M X _ _ _ _ e B hn b
  exact operator_bilinear_normal_preservation e B hn b

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem normal_reduction {n : ℕ} (hn : 1 ≤ n) (f : Cochain M (n+1))
    (hf : ∀ v, differentialValue f v = 0) :
    ∃ (F : Cochain M (n+1)) (b : Cochain M n),
      SeparatelyNormal e F ∧
      (∀ v, differentialValue F v = 0) ∧
      (∀ v, f v = F v + differentialValue b v) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact normal_reduction_of_bilinear_preservation e
    ((bilinear_preservation_iff e).mpr (operator_bilinear_normal_preservation e)) f hf

theorem normal_reduction_any {A : Type u} {Y : Type v} [CStarAlgebra A]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (E : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] A)
    {n : ℕ} (hn : 1 ≤ n) (f : Cochain A (n+1))
    (hf : ∀ v, differentialValue f v = 0) :
    ∃ (F : Cochain A (n+1)) (b : Cochain A n),
      SeparatelyNormal E F ∧
      (∀ v, differentialValue F v = 0) ∧
      (∀ v, f v = F v + differentialValue b v) := by
  obtain ⟨Z,hZ,hZS,hZC,⟨T⟩⟩ := exists_same_universe_predual E
  let := hZ
  let := hZS
  let := hZC
  let EZ : StrongDual ℂ Z ≃ₗᵢ⋆[ℂ] A := (dualIsometry T).trans E
  obtain ⟨F,b,hFN,hFc,hid⟩ := normal_reduction EZ hn f hf
  refine ⟨F,b,?_,hFc,hid⟩
  intro i v y
  obtain ⟨z,hz⟩ := hFN i v (T.symm y)
  refine ⟨T z,fun a => ?_⟩
  have h := hz a
  change E.symm (F (Function.update v i a)) (T (T.symm y)) = E.symm a (T z) at h
  simpa only [T.apply_symm_apply] using h

def NormalReductionGoal : Prop :=
  ∀ (M X : Type*) [CStarAlgebra M]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (n : ℕ), 1 ≤ n →
    ∀ (f : Cochain M (n+1)),
    (∀ v : Fin (n+1+1) → M, differentialValue f v = 0) →
    ∃ (F : Cochain M (n+1)) (b : Cochain M n),
      SeparatelyNormal e F ∧
      (∀ v : Fin (n+1+1) → M, differentialValue F v = 0) ∧
      (∀ v : Fin (n+1) → M, f v = F v + differentialValue b v)

theorem normalReductionGoal_proved : NormalReductionGoal := by
  intro M X _ _ _ _ e n hn f hf
  exact normal_reduction_any e hn f hf

end BoundedHochschild

end

end OAI
