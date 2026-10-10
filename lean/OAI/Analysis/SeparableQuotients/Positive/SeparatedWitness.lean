import OAI.Analysis.SeparableQuotients.Positive.ComplexSequences
import OAI.Analysis.SeparableQuotients.Positive.RealWitness

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.ComplexTransfer
open Set TopologicalSpace Scalar
attribute [local instance] Scalar.dualSubmoduleNormedGroup Scalar.dualSubmoduleNormedSpace
attribute [local instance] realDualSubmoduleNormedGroup realDualSubmoduleNormedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]

local instance complexDualSubmoduleRealNormedSpace (H : Submodule ℂ (StrongDual ℂ X)) :
    NormedSpace ℝ H := Submodule.normedSpace (H.restrictScalars ℝ)

local instance complexRealOperatorNormedGroup (H : Submodule ℂ (StrongDual ℂ X)) :
    NormedAddCommGroup (H →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance complexRealOperatorMetric (H : Submodule ℂ (StrongDual ℂ X)) :
    PseudoMetrizableSpace (H →L[ℝ] ℂ) :=
  @PseudoEMetricSpace.pseudoMetrizableSpace (H →L[ℝ] ℂ)
    (inferInstance : PseudoEMetricSpace (H →L[ℝ] ℂ))
local instance complexRealOperatorNormedSpace (H : Submodule ℂ (StrongDual ℂ X)) :
    NormedSpace ℂ (H →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance complexRealOperatorAdd (H : Submodule ℂ (StrongDual ℂ X)) :
    ContinuousAdd (H →L[ℝ] ℂ) := ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
local instance complexRealOperatorSMul (H : Submodule ℂ (StrongDual ℂ X)) :
    ContinuousSMul ℂ (H →L[ℝ] ℂ) :=
  @IsBoundedSMul.continuousSMul ℂ (H →L[ℝ] ℂ) _
    (inferInstance : PseudoMetricSpace (H →L[ℝ] ℂ)) _ _ _
    (@NormedSpace.toIsBoundedSMul ℂ (H →L[ℝ] ℂ) _
      (inferInstance : SeminormedAddCommGroup (H →L[ℝ] ℂ))
      (inferInstance : NormedSpace ℂ (H →L[ℝ] ℂ)))
local instance complexRealOperatorT2 (H : Submodule ℂ (StrongDual ℂ X)) :
    T2Space (H →L[ℝ] ℂ) :=
  letI : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul
  ContinuousLinearMap.instT2Space (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)

lemma complex_eval_separable_of_real (H : Submodule ℂ (StrongDual ℂ X))
    (hs : IsSeparable (Set.range (realEvaluation (H.restrictScalars ℝ)))) :
    IsSeparable (Set.range (Scalar.evaluation H)) := by
  apply ((ContinuousLinearMap.isEmbedding_restrictScalars (𝕜 := ℂ)
    (E := H) (F := ℂ) ℝ).isInducing.isSeparable_preimage hs).mono
  rintro _ ⟨x, rfl⟩
  exact ⟨x, rfl⟩

lemma separable_evaluation_of_coordinates
    (E : Submodule ℝ (StrongDual ℂ X))
    (hEsep : IsSeparable (Set.range (realEvaluation E)))
    (H : Submodule ℂ (StrongDual ℂ X)) (P Q : H →L[ℝ] E)
    (hPQ : ∀ h : H, (h : StrongDual ℂ X) = (P h : StrongDual ℂ X) +
      Complex.I • (Q h : StrongDual ℂ X)) :
    IsSeparable (Set.range (Scalar.evaluation H)) := by
  apply complex_eval_separable_of_real
  let φ : (E →L[ℝ] ℂ) → (H →L[ℝ] ℂ) := fun e => e.comp P + Complex.I • e.comp Q
  have hφ : Continuous φ := by fun_prop
  apply (hEsep.image hφ).mono
  rintro _ ⟨x, rfl⟩
  refine ⟨realEvaluation E x, Set.mem_range_self _, ?_⟩
  ext h
  change (P h : StrongDual ℂ X) x + Complex.I * (Q h : StrongDual ℂ X) x =
    (h : StrongDual ℂ X) x
  exact congrArg (fun f : StrongDual ℂ X => f x) (hPQ h).symm

theorem complex_witness_of_separated
    (E : Submodule ℝ (StrongDual ℂ X))
    (hEsep : IsSeparable (Set.range (realEvaluation E)))
    (hsep : HasSeparatedInfiniteSubspace E) :
    ∃ H : Submodule ℂ (StrongDual ℂ X), IsClosed (H : Set (StrongDual ℂ X)) ∧
      ¬ FiniteDimensional ℂ H ∧ IsSeparable (Set.range (Scalar.evaluation H)) := by
  obtain ⟨W, hWE, hWcl, hWinf, C, hC, hsep⟩ := hsep
  obtain ⟨H, hHcl, hHinf, P, Q, hPQ⟩ :=
    complex_subspace_of_separated E W hWE hWcl hWinf hC hsep
  exact ⟨H, hHcl, hHinf, separable_evaluation_of_coordinates E hEsep H P Q hPQ⟩

end SeparableQuotient.Positive.Fields.ComplexTransfer

end

end

end OAI
