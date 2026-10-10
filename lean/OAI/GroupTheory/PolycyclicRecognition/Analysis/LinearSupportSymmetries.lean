import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportSymmetries

namespace OAI

/-! # Algebraic support symmetries

The finite symmetry conclusion does not require a preselected norm or
topology on the finite-dimensional height quotient.
-/

noncomputable section

namespace PolycyclicRecognition

variable {W I B : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
  [Fintype I] [Fintype B] [Nonempty B]

/-- The support norm supplies the topology used to prove finiteness. The
result concerns the original algebraic linear equivalences. -/
theorem finite_linear_support_isometries (D : SupportDatum W I B) :
    Set.Finite {A : W ≃ₗ[ℝ] W | ∀ w, D.segmentSupport (A w) = D.segmentSupport w} := by
  let : Norm W := ⟨D.segmentSupport⟩
  let core : NormedSpace.Core ℝ W := D.normCore
  let : NormedAddCommGroup W := NormedAddCommGroup.ofCore core
  let : NormedSpace ℝ W := NormedSpace.ofCore core
  let Labels := {A : W ≃ₗ[ℝ] W // ∀ w, D.segmentSupport (A w) = D.segmentSupport w}
  let ContinuousLabels := {A : W ≃L[ℝ] W // ∀ w, D.segmentSupport (A w) = D.segmentSupport w}
  have : Finite ContinuousLabels := (finite_support_isometries D).to_subtype
  let f : Labels → ContinuousLabels := fun A => ⟨A.val.toContinuousLinearEquiv, A.property⟩
  have hf : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    ext w
    exact congrArg (fun A : ContinuousLabels => A.val w) h
  have : Finite Labels := Finite.of_injective f hf
  exact Set.finite_coe_iff.mp this

/-- The algebraic finite group of possible segment-support symmetries. -/
def linearSupportSymmetryGroup (D : SupportDatum W I B) : Subgroup (W ≃ₗ[ℝ] W) where
  carrier := {A | ∀ w, D.segmentSupport (A w) = D.segmentSupport w}
  one_mem' := fun _ => rfl
  mul_mem' := fun hA hB w => (hA _).trans (hB w)
  inv_mem' := by
    intro A hA w
    change D.segmentSupport (A.symm w) = D.segmentSupport w
    simpa only [LinearEquiv.apply_symm_apply] using (hA (A.symm w)).symm

instance (D : SupportDatum W I B) : Finite (linearSupportSymmetryGroup D) :=
  (finite_linear_support_isometries D).to_subtype

end PolycyclicRecognition

end

end OAI
