import OAI.Analysis.KadisonSimilarity.Tensor.EndpointTensors

namespace OAI

/-!
# The finite-stage coefficient form

The coefficient function used by the invariant argument is proved multilinear
from the linear source letters and conjugate-linear test letters. No finite or
completed coefficient expansion is part of this construction.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexConjugate TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The elementary completed word retains multilinearity in every letter. -/
theorem completedTensorWord_update_add {n : ℕ} (x : Fin n → F) (i : Fin n) (a b : F) :
    completedTensorWord (Function.update x i (a + b)) =
      completedTensorWord (Function.update x i a) + completedTensorWord (Function.update x i b) := by
  have h := (tensorWordMultilinear n).map_update_add x i a b
  simpa only [tensorWordMultilinear_apply, completedTensorWord,
    UniformSpace.Completion.coe_add] using congrArg
      (fun z : TensorWord F n => (z : CompletedTensorWord F n)) h

theorem completedTensorWord_update_smul {n : ℕ} (x : Fin n → F) (i : Fin n) (c : ℂ) (a : F) :
    completedTensorWord (Function.update x i (c • a)) =
      c • completedTensorWord (Function.update x i a) := by
  have h := (tensorWordMultilinear n).map_update_smul x i c a
  simpa only [tensorWordMultilinear_apply, completedTensorWord,
    UniformSpace.Completion.coe_smul] using congrArg
      (fun z : TensorWord F n => (z : CompletedTensorWord F n)) h

theorem endpointWord_add_endpoint {n : ℕ} (d c : E) (x : Fin n → F) :
    endpointWord (d + c) x = endpointWord d x + endpointWord c x := by
  exact (congrArg
    (fun z : E ⊗[ℂ] CompletedTensorWord F n =>
      (z : HilbertTensor E (CompletedTensorWord F n)))
    (TensorProduct.add_tmul d c (completedTensorWord x))).trans
      (hilbertTensor_coe_add _ _)

theorem endpointWord_smul_endpoint {n : ℕ} (c : ℂ) (d : E) (x : Fin n → F) :
    endpointWord (c • d) x = c • endpointWord d x := by
  exact (congrArg
    (fun z : E ⊗[ℂ] CompletedTensorWord F n =>
      (z : HilbertTensor E (CompletedTensorWord F n)))
    (TensorProduct.smul_tmul' c d (completedTensorWord x)).symm).trans
      (UniformSpace.Completion.coe_smul c (d ⊗ₜ[ℂ] completedTensorWord x))

theorem endpointWord_update_add {n : ℕ} (d : E) (x : Fin n → F) (i : Fin n) (a b : F) :
    endpointWord d (Function.update x i (a + b)) =
      endpointWord d (Function.update x i a) + endpointWord d (Function.update x i b) := by
  simp only [endpointWord, completedTensorWord_update_add, map_add]

theorem endpointWord_update_smul {n : ℕ} (d : E) (x : Fin n → F) (i : Fin n) (c : ℂ) (a : F) :
    endpointWord d (Function.update x i (c • a)) =
      c • endpointWord d (Function.update x i a) := by
  simp only [endpointWord, completedTensorWord_update_smul, map_smul]

private def pullLetters {D V I S : Type*} (f : D → V) (j : I → S) (v : S → D) : I → V :=
  f ∘ v ∘ j

private theorem pullLetters_update {D V I S : Type*} [DecidableEq I] [DecidableEq S]
    (f : D → V) (j : I → S) (hj : Function.Injective j) (v : S → D) (i : I) (a : D) :
    pullLetters f j (Function.update v (j i) a) =
      Function.update (pullLetters f j v) i (f a) := by
  unfold pullLetters
  rw [Function.update_comp_eq_of_injective v hj i a,
    Function.comp_update]

private theorem pullLetters_update_miss {D V I S : Type*} [DecidableEq S]
    (f : D → V) (j : I → S) (v : S → D) (i : S) (a : D) (hmiss : ∀ x, j x ≠ i) :
    pullLetters f j (Function.update v i a) = pullLetters f j v := by
  unfold pullLetters
  rw [Function.update_comp_eq_of_forall_ne v a hmiss]

private abbrev sourceIndex {k l : ℕ} (i : Fin k) : Option (Fin k ⊕ Fin l) := some (Sum.inl i)
private abbrev testIndex {k l : ℕ} (i : Fin l) : Option (Fin k ⊕ Fin l) := some (Sum.inr i)

variable {D : Type*} [AddCommGroup D] [Module ℂ D] {k l : ℕ}

/-- The coefficient with distinguished endpoint and two groups of tail letters. -/
def invariantStageCoefficient
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) (Ω : E)
    (testEndpoint : D →ₗ⋆[ℂ] E) (sourceLetter : D →ₗ[ℂ] F)
    (testLetter : D →ₗ⋆[ℂ] F) (v : Option (Fin k ⊕ Fin l) → D) : ℂ :=
  inner ℂ (endpointWord (testEndpoint (v none)) (pullLetters testLetter testIndex v))
    (Y (endpointWord Ω (pullLetters sourceLetter sourceIndex v)))

/-- Multilinearity of the actual finite-stage coefficient function. -/
def invariantStageForm
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) (Ω : E)
    (testEndpoint : D →ₗ⋆[ℂ] E) (sourceLetter : D →ₗ[ℂ] F)
    (testLetter : D →ₗ⋆[ℂ] F) :
    MultilinearMap ℂ (fun _ : Option (Fin k ⊕ Fin l) => D) ℂ :=
  MultilinearMap.mk' (invariantStageCoefficient Y Ω testEndpoint sourceLetter testLetter)
    (by
      intro v i a b
      cases i with
      | none =>
        have hs (a : D) : pullLetters sourceLetter (@sourceIndex k l) (Function.update v none a) =
            pullLetters sourceLetter sourceIndex v :=
          pullLetters_update_miss sourceLetter sourceIndex v none a (by intro j; simp)
        have ht (a : D) : pullLetters testLetter (@testIndex k l) (Function.update v none a) =
            pullLetters testLetter testIndex v :=
          pullLetters_update_miss testLetter testIndex v none a (by intro j; simp)
        simp only [invariantStageCoefficient, Function.update_self, hs, ht, map_add,
          endpointWord_add_endpoint, inner_add_left]
      | some i =>
        cases i with
        | inl i =>
          have hi : Function.Injective (@sourceIndex k l) := by intro a b h; simpa using h
          have hp (a : D) : pullLetters sourceLetter sourceIndex (Function.update v (sourceIndex i) a) =
              Function.update (pullLetters sourceLetter sourceIndex v) i (sourceLetter a) :=
            pullLetters_update sourceLetter sourceIndex hi v i a
          have hm (a : D) : pullLetters testLetter testIndex (Function.update v (sourceIndex i) a) =
              pullLetters testLetter testIndex v :=
            pullLetters_update_miss testLetter testIndex v (sourceIndex i) a (by intro j; simp)
          have hn (a : D) : Function.update v (sourceIndex i) a none = v none :=
            Function.update_of_ne (by simp) a v
          simp only [invariantStageCoefficient, hn, hp, hm, map_add,
            endpointWord_update_add, inner_add_right]
        | inr i =>
          have hi : Function.Injective (@testIndex k l) := by intro a b h; simpa using h
          have hp (a : D) : pullLetters testLetter testIndex (Function.update v (testIndex i) a) =
              Function.update (pullLetters testLetter testIndex v) i (testLetter a) :=
            pullLetters_update testLetter testIndex hi v i a
          have hm (a : D) : pullLetters sourceLetter sourceIndex (Function.update v (testIndex i) a) =
              pullLetters sourceLetter sourceIndex v :=
            pullLetters_update_miss sourceLetter sourceIndex v (testIndex i) a (by intro j; simp)
          have hn (a : D) : Function.update v (testIndex i) a none = v none :=
            Function.update_of_ne (by simp) a v
          simp only [invariantStageCoefficient, hn, hp, hm, map_add,
            endpointWord_update_add, inner_add_left])
    (by
      intro v i c a
      cases i with
      | none =>
        have hs (a : D) : pullLetters sourceLetter (@sourceIndex k l) (Function.update v none a) =
            pullLetters sourceLetter sourceIndex v :=
          pullLetters_update_miss sourceLetter sourceIndex v none a (by intro j; simp)
        have ht (a : D) : pullLetters testLetter (@testIndex k l) (Function.update v none a) =
            pullLetters testLetter testIndex v :=
          pullLetters_update_miss testLetter testIndex v none a (by intro j; simp)
        simp only [invariantStageCoefficient, Function.update_self, hs, ht, map_smulₛₗ,
          starRingEnd_apply, endpointWord_smul_endpoint, inner_smul_left, star_star, smul_eq_mul]
      | some i =>
        cases i with
        | inl i =>
          have hi : Function.Injective (@sourceIndex k l) := by intro a b h; simpa using h
          have hp (a : D) : pullLetters sourceLetter sourceIndex (Function.update v (sourceIndex i) a) =
              Function.update (pullLetters sourceLetter sourceIndex v) i (sourceLetter a) :=
            pullLetters_update sourceLetter sourceIndex hi v i a
          have hm (a : D) : pullLetters testLetter testIndex (Function.update v (sourceIndex i) a) =
              pullLetters testLetter testIndex v :=
            pullLetters_update_miss testLetter testIndex v (sourceIndex i) a (by intro j; simp)
          have hn (a : D) : Function.update v (sourceIndex i) a none = v none :=
            Function.update_of_ne (by simp) a v
          simp only [invariantStageCoefficient, hn, hp, hm, map_smulₛₗ, RingHom.id_apply,
            endpointWord_update_smul, inner_smul_right, smul_eq_mul]
        | inr i =>
          have hi : Function.Injective (@testIndex k l) := by intro a b h; simpa using h
          have hp (a : D) : pullLetters testLetter testIndex (Function.update v (testIndex i) a) =
              Function.update (pullLetters testLetter testIndex v) i (testLetter a) :=
            pullLetters_update testLetter testIndex hi v i a
          have hm (a : D) : pullLetters sourceLetter sourceIndex (Function.update v (testIndex i) a) =
              pullLetters sourceLetter sourceIndex v :=
            pullLetters_update_miss sourceLetter sourceIndex v (testIndex i) a (by intro j; simp)
          have hn (a : D) : Function.update v (testIndex i) a none = v none :=
            Function.update_of_ne (by simp) a v
          simp only [invariantStageCoefficient, hn, hp, hm, map_smulₛₗ,
            starRingEnd_apply, endpointWord_update_smul, inner_smul_left, star_star, smul_eq_mul])

@[simp] theorem invariantStageForm_apply
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) (Ω : E)
    (testEndpoint : D →ₗ⋆[ℂ] E) (sourceLetter : D →ₗ[ℂ] F)
    (testLetter : D →ₗ⋆[ℂ] F) (v : Option (Fin k ⊕ Fin l) → D) :
    invariantStageForm Y Ω testEndpoint sourceLetter testLetter v =
      inner ℂ (endpointWord (testEndpoint (v none)) (fun j => testLetter (v (some (Sum.inr j)))))
        (Y (endpointWord Ω (fun i => sourceLetter (v (some (Sum.inl i)))))) := rfl

end KadisonSimilarity

end

end OAI
