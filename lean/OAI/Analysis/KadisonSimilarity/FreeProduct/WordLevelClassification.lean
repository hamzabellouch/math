import OAI.Analysis.KadisonSimilarity.Tensor.MultiplicityClassification

namespace OAI

/-!
# Different multiplicities and the orthogonal word-level decomposition

Source and target word levels have independent Hilbert multiplicity spaces.
Their scalar slices are bounded endpoint intertwiners, so unequal degrees
vanish by the completed endpoint classification.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {Gsource Gtarget H K : Type*}
  [NormedAddCommGroup Gsource] [InnerProductSpace ℂ Gsource]
  [NormedAddCommGroup Gtarget] [InnerProductSpace ℂ Gtarget]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A bounded scalar multiplicity slice with independently typed source and
target multiplicities. -/
def crossMultiplicitySlice
    (Y : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K)
    (a : Gsource) (b : Gtarget) : H →L[ℂ] K :=
  (tensorSlice b).comp (Y.comp (hilbertTensorInsert a))

/-- Distinct source and target multiplicities do not affect the tensor
intertwining calculation. -/
theorem crossMultiplicitySlice_intertwines
    (Y : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K)
    (S : H →L[ℂ] H) (T : K →L[ℂ] K)
    (hY : Y.comp (hilbertTensorLift S) = (hilbertTensorLift T).comp Y)
    (a : Gsource) (b : Gtarget) :
    (crossMultiplicitySlice Y a b).comp S = T.comp (crossMultiplicitySlice Y a b) := by
  ext x
  have heq := congrArg (fun A : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K =>
    A (hilbertTensorInsert a x)) hY
  simp only [ContinuousLinearMap.comp_apply, hilbertTensorLift_insert] at heq
  change tensorSlice b (Y (hilbertTensorInsert a (S x))) =
    T (tensorSlice b (Y (hilbertTensorInsert a x)))
  rw [heq]
  exact congrArg (fun A : HilbertTensor Gtarget K →L[ℂ] K =>
    A (Y (hilbertTensorInsert a x))) (tensorSlice_lift T b)

/-- Cross-multiplicity slices are the actual elementary tensor coefficients. -/
theorem inner_crossMultiplicitySlice
    (Y : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K)
    (a : Gsource) (b : Gtarget) (x : H) (z : K) :
    inner ℂ z (crossMultiplicitySlice Y a b x) =
      inner ℂ (hilbertTensorInsert b z) (Y (hilbertTensorInsert a x)) := by
  change inner ℂ z (tensorSlice b (Y (hilbertTensorInsert a x))) = _
  generalize Y (hilbertTensorInsert a x) = w
  induction w using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih w =>
    induction w using TensorProduct.inductionOn with
    | tmul c y =>
      change inner ℂ z (tensorSlice b (hilbertTensorInsert c y)) =
        inner ℂ (hilbertTensorInsert b z) (hilbertTensorInsert c y)
      rw [tensorSlice_insert, inner_smul_right, inner_hilbertTensorInsert]
    | add u v hu hv =>
      have hs : tensorSlice b ((u + v : Gtarget ⊗[ℂ] K) : HilbertTensor Gtarget K) =
          tensorSlice b (u : HilbertTensor Gtarget K) + tensorSlice b (v : HilbertTensor Gtarget K) :=
        (congrArg (tensorSlice b) (hilbertTensor_coe_add u v)).trans
          ((tensorSlice b).map_add _ _)
      calc
        _ = inner ℂ z (tensorSlice b (u : HilbertTensor Gtarget K) +
              tensorSlice b (v : HilbertTensor Gtarget K)) := congrArg (fun y => inner ℂ z y) hs
        _ = inner ℂ z (tensorSlice b (u : HilbertTensor Gtarget K)) +
              inner ℂ z (tensorSlice b (v : HilbertTensor Gtarget K)) := inner_add_right _ _ _
        _ = inner ℂ (hilbertTensorInsert b z) (u : HilbertTensor Gtarget K) +
              inner ℂ (hilbertTensorInsert b z) (v : HilbertTensor Gtarget K) := congrArg₂ (· + ·) hu hv
        _ = _ := ((congrArg (fun y => inner ℂ (hilbertTensorInsert b z) y)
            (hilbertTensor_coe_add u v)).trans (inner_add_right _ _ _)).symm

/-- All cross-multiplicity slices determine the entire bounded operator. -/
theorem crossMultiplicitySlice_ext
    (Y Z : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K)
    (hslice : ∀ a b, crossMultiplicitySlice Y a b = crossMultiplicitySlice Z a b) : Y = Z := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  apply hilbertTensor_ext_inner_insert
  intro b z
  rw [← inner_crossMultiplicitySlice, ← inner_crossMultiplicitySlice, hslice]

@[simp] theorem crossMultiplicitySlice_zero (a : Gsource) (b : Gtarget) :
    crossMultiplicitySlice (0 : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K) a b = 0 := by
  ext x
  simp [crossMultiplicitySlice]

section EndpointLevels

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {α : Type*} [Fintype α] [DecidableEq α] {k l : ℕ}

/-- Actual word covariance for an operator between independent multiplicity
spaces. The word formulas refer only to the common endpoint and tail factors. -/
structure CrossMultiplicityMatrixCovariance
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : HilbertTensor Gsource (EndpointTensor E F k) →L[ℂ]
      HilbertTensor Gtarget (EndpointTensor E F l)) where
  sourceAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F k →ₗᵢ[ℂ] EndpointTensor E F k
  testAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F l →ₗᵢ[ℂ] EndpointTensor E F l
  intertwine : ∀ u, Y.comp (hilbertTensorLift (sourceAction u).toContinuousLinearMap) =
    (hilbertTensorLift (testAction u).toContinuousLinearMap).comp Y
  source_covariance : ∀ (u : Matrix.unitaryGroup α ℂ)
      (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord Ω (fun i => R.center
      ((u : Matrix α α ℂ) * v (some (Sum.inl i)) * star (u : Matrix α α ℂ))) =
      sourceAction u (endpointWord Ω (fun i => R.center (v (some (Sum.inl i)))))
  test_covariance : ∀ (u : Matrix.unitaryGroup α ℂ)
      (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord (R.full (star
      ((u : Matrix α α ℂ) * v none * star (u : Matrix α α ℂ))))
      (fun j => J (R.center
        ((u : Matrix α α ℂ) * v (some (Sum.inr j)) * star (u : Matrix α α ℂ)))) =
      testAction u (endpointWord (R.full (star (v none)))
        (fun j => J (R.center (v (some (Sum.inr j))))))

/-- Actual covariance passes to a scalar cross-multiplicity slice. -/
def CrossMultiplicityMatrixCovariance.slice
    {R : MatrixHilbertStage (E := E) (F := F) (α := α)} {J : F →ₗᵢ⋆[ℂ] F}
    {Ω : E} {Y : HilbertTensor Gsource (EndpointTensor E F k) →L[ℂ]
      HilbertTensor Gtarget (EndpointTensor E F l)}
    (cov : CrossMultiplicityMatrixCovariance R J Ω Y) (a : Gsource) (b : Gtarget) :
    MatrixWordCovariance R J Ω (crossMultiplicitySlice Y a b) where
  sourceAction := cov.sourceAction
  testAction := cov.testAction
  intertwine u := crossMultiplicitySlice_intertwines Y _ _ (cov.intertwine u) a b
  source_covariance := cov.source_covariance
  test_covariance := cov.test_covariance

variable {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- The unequal-degree theorem applies with entirely different source and
target multiplicity Hilbert spaces. -/
theorem crossMultiplicity_intertwiner_zero_of_schurWeyl
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : HilbertTensor Gsource (EndpointTensor E F k) →L[ℂ]
      HilbertTensor Gtarget (EndpointTensor E F l))
    (hleft : ∀ s a,
      Y.comp (hilbertTensorLift (endpointHeadAction (n := k) ((T.stage s).left a))) =
      (hilbertTensorLift (endpointHeadAction (n := l) ((T.stage s).left a))).comp Y)
    (cov : ∀ s, CrossMultiplicityMatrixCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) (hkl : k ≠ l) : Y = 0 := by
  apply crossMultiplicitySlice_ext
  intro a b
  rw [crossMultiplicitySlice_zero]
  exact endpoint_intertwiner_zero_of_schurWeyl T (crossMultiplicitySlice Y a b)
    (fun s c => crossMultiplicitySlice_intertwines Y _ _ (hleft s c) a b)
    (fun s => (cov s).slice a b) spanning hcontraction labels hlabels hkl

end EndpointLevels

end KadisonSimilarity

end

end OAI
