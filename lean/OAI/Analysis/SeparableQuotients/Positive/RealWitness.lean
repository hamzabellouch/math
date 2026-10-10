import OAI.Analysis.SeparableQuotients.Positive.ScalarQuotients

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.ComplexTransfer
open Set TopologicalSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
attribute [local instance] Scalar.dualSubmoduleNormedGroup Scalar.dualSubmoduleNormedSpace
local instance realDualSubmoduleNormedGroup (E : Submodule ℝ (StrongDual ℂ X)) :
    NormedAddCommGroup E := Submodule.normedAddCommGroup E
local instance realDualSubmoduleNormedSpace (E : Submodule ℝ (StrongDual ℂ X)) :
    NormedSpace ℝ E := Submodule.normedSpace E



def realEvaluation (E : Submodule ℝ (StrongDual ℂ X)) :
    X →L[ℝ] (E →L[ℝ] ℂ) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ X ℂ ℝ ℝ).comp E.subtypeL).flip

@[simp] lemma realEvaluation_apply (E : Submodule ℝ (StrongDual ℂ X))
    (x : X) (f : E) : realEvaluation E x f = (f : StrongDual ℂ X) x := rfl



theorem transport_real_witness
    (E : Submodule ℝ (StrongDual ℝ X)) (hEclosed : IsClosed (E : Set (StrongDual ℝ X)))
    (hEinf : ¬ FiniteDimensional ℝ E)
    (hEsep : IsSeparable (Set.range (Scalar.evaluation E))) :
    ∃ F : Submodule ℝ (StrongDual ℂ X),
      IsClosed (F : Set (StrongDual ℂ X)) ∧ ¬ FiniteDimensional ℝ F ∧
        IsSeparable (Set.range (realEvaluation F)) := by
  let A : StrongDual ℝ X ≃L[ℝ] StrongDual ℂ X :=
    StrongDual.extendRCLikeL
  let F : Submodule ℝ (StrongDual ℂ X) := E.map A.toLinearEquiv.toLinearMap
  let e : E ≃L[ℝ] F := A.submoduleMap E
  have hFclosed : IsClosed (F : Set (StrongDual ℂ X)) :=
    A.toHomeomorph.isClosedMap _ hEclosed
  have hFinf : ¬ FiniteDimensional ℝ F := by
    intro hh
    let := hh
    exact hEinf e.symm.toLinearEquiv.finiteDimensional
  let φ : (StrongDual ℝ E × StrongDual ℝ E) → (F →L[ℝ] ℂ) := fun p =>
    ((Complex.ofRealCLM.comp p.1 - Complex.I • (Complex.ofRealCLM.comp p.2)).comp
      e.symm.toContinuousLinearMap)
  have hφ : Continuous φ := by fun_prop
  have hsep : IsSeparable (φ '' (Set.range (Scalar.evaluation E) ×ˢ
      Set.range (Scalar.evaluation E))) := (hEsep.prod hEsep).image hφ
  refine ⟨F, hFclosed, hFinf, hsep.mono ?_⟩
  rintro _ ⟨x, rfl⟩
  refine ⟨(Scalar.evaluation E x, Scalar.evaluation E (Complex.I • x)),
    ⟨Set.mem_range_self _, Set.mem_range_self _⟩, ?_⟩
  ext f
  change ((e.symm f : E) : StrongDual ℝ X) x - Complex.I *
    (((e.symm f : E) : StrongDual ℝ X) (Complex.I • x) : ℂ) = (f : StrongDual ℂ X) x
  have he : A ((e.symm f : E) : StrongDual ℝ X) = (f : StrongDual ℂ X) :=
    congrArg Subtype.val (e.apply_symm_apply f)
  rw [← he]
  change _ = StrongDual.extendRCLike ((e.symm f : E) : StrongDual ℝ X) x
  rw [StrongDual.extendRCLike_apply]
  rfl

end SeparableQuotient.Positive.Fields.ComplexTransfer

end

end

end OAI
