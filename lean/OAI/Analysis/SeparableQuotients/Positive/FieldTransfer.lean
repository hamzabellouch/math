import OAI.Analysis.SeparableQuotients.Positive.ComplexPerturbation

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



theorem complex_witness_of_real
    (E : Submodule ℝ (StrongDual ℂ X)) (hEcl : IsClosed (E : Set (StrongDual ℂ X)))
    (hEinf : ¬ FiniteDimensional ℝ E) (hEsep : IsSeparable (Set.range (realEvaluation E))) :
    ∃ H : Submodule ℂ (StrongDual ℂ X), IsClosed (H : Set (StrongDual ℂ X)) ∧
      ¬ FiniteDimensional ℂ H ∧ IsSeparable (Set.range (Scalar.evaluation H)) := by
  classical
  by_cases hs : HasSeparatedInfiniteSubspace E
  · exact complex_witness_of_separated E hEsep hs
  · obtain ⟨f, g, D, hv, hD, hnorm, hann, hfg⟩ :=
      exists_near_prefix_sequence E hEcl hEinf hs
    exact perturbation_witness E hEcl hEsep f g
      (prefixBound_of_half_normers ℂ _ D hD hnorm hann) hv (fun n => (hfg n).le)




theorem positive_transfer [CompleteSpace X]
    (h : HasSeparableQuotient ℝ X) : HasSeparableQuotient ℂ X := by
  obtain ⟨E, hEcl, hEinf, hEsep⟩ := Scalar.evaluation_criterion.mp h
  obtain ⟨F, hFcl, hFinf, hFsep⟩ := transport_real_witness E hEcl hEinf hEsep
  obtain ⟨H, hHcl, hHinf, hHsep⟩ := complex_witness_of_real F hFcl hFinf hFsep
  exact Scalar.evaluation_criterion.mpr ⟨H, hHcl, hHinf, hHsep⟩

end SeparableQuotient.Positive.Fields.ComplexTransfer

end

end

end OAI
