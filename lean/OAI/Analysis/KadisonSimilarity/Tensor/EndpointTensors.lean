import OAI.Analysis.KadisonSimilarity.Tensor.TensorClassification
import OAI.Analysis.KadisonSimilarity.Tensor.EndpointBounds

namespace OAI

/-!
# Completed tensor words with an unrestricted first endpoint

The endpoint and the centered tail may live in different Hilbert spaces.
Their completed tensor product has total elementary words and carries
the operators `I ⊗ A` and endpoint slices.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

@[simp] theorem inner_hilbertTensor_coe (x y : E ⊗[ℂ] F) :
    inner ℂ (x : HilbertTensor E F) (y : HilbertTensor E F) = inner ℂ x y :=
  UniformSpace.Completion.inner_coe x y

@[simp] theorem hilbertTensor_coe_add (x y : E ⊗[ℂ] F) :
    ((x + y : E ⊗[ℂ] F) : HilbertTensor E F) =
      (x : HilbertTensor E F) + (y : HilbertTensor E F) :=
  UniformSpace.Completion.coe_add x y

/-- An unrestricted endpoint followed by a completed centered tail. -/
abbrev EndpointTensor (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (n : ℕ) :=
  HilbertTensor E (CompletedTensorWord F n)

/-- Insert an endpoint in front of a completed tail vector. -/
def endpointInsert {n : ℕ} (d : E) :
    CompletedTensorWord F n →L[ℂ] EndpointTensor E F n :=
  UniformSpace.Completion.toComplL.comp (TensorProduct.mkL ℂ E (CompletedTensorWord F n) d)

/-- The elementary word with an unrestricted first endpoint. -/
def endpointWord {n : ℕ} (d : E) (x : Fin n → F) : EndpointTensor E F n :=
  endpointInsert d (completedTensorWord x)

@[simp] theorem endpointInsert_apply {n : ℕ} (d : E) (w : CompletedTensorWord F n) :
    endpointInsert d w = (d ⊗ₜ[ℂ] w : E ⊗[ℂ] CompletedTensorWord F n) := rfl

@[simp] theorem norm_endpointInsert {n : ℕ} (d : E) (w : CompletedTensorWord F n) :
    ‖endpointInsert d w‖ = ‖d‖ * ‖w‖ := by
  exact (UniformSpace.Completion.norm_coe (d ⊗ₜ[ℂ] w)).trans
    (TensorProduct.norm_tmul d w)

theorem norm_endpointInsert_le {n : ℕ} (d : E) :
    ‖endpointInsert (F := F) (n := n) d‖ ≤ ‖d‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro w
  rw [norm_endpointInsert]

@[simp] theorem inner_endpointInsert {n : ℕ} (d c : E)
    (x z : CompletedTensorWord F n) :
    inner ℂ (endpointInsert d x) (endpointInsert c z) = inner ℂ d c * inner ℂ x z := by
  exact (UniformSpace.Completion.inner_coe (d ⊗ₜ[ℂ] x) (c ⊗ₜ[ℂ] z)).trans
    (TensorProduct.inner_tmul ℂ d c x z)

@[simp] theorem inner_endpointWord {n : ℕ} (d c : E) (x z : Fin n → F) :
    inner ℂ (endpointWord d x) (endpointWord c z) =
      inner ℂ d c * ∏ i, inner ℂ (x i) (z i) := by
  rw [endpointWord, endpointWord, inner_endpointInsert, inner_completedTensorWord]

/-- Endpoint words are total in the completed endpoint tensor product. -/
theorem endpointWord_mem_closed_submodule {n : ℕ}
    (S : Submodule ℂ (EndpointTensor E F n)) (hclosed : IsClosed (S : Set (EndpointTensor E F n)))
    (hword : ∀ d x, endpointWord d x ∈ S) (z : EndpointTensor E F n) : z ∈ S := by
  unfold EndpointTensor HilbertTensor at *
  have hpair (d : E) (w : CompletedTensorWord F n) : endpointInsert d w ∈ S := by
    let T : Submodule ℂ (CompletedTensorWord F n) := S.comap (endpointInsert (F := F) (n := n) d).toLinearMap
    apply completedTensorWord_mem_closed_submodule T
      (hclosed.preimage (endpointInsert d).continuous) (hword d) w
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul d w => exact hpair d w
    | add x y hx hy =>
      change ((x + y : E ⊗[ℂ] CompletedTensorWord F n) : EndpointTensor E F n) ∈ S
      simpa only [UniformSpace.Completion.coe_add] using S.add_mem hx hy

/-- Continuous linear maps on endpoint words are determined by elementary words. -/
theorem continuousLinearMap_ext_endpointWords {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] {n : ℕ}
    (f g : EndpointTensor E F n →L[ℂ] G)
    (hword : ∀ d x, f (endpointWord d x) = g (endpointWord d x)) : f = g := by
  let S : Submodule ℂ (EndpointTensor E F n) := (f - g).ker
  have hmem (z : EndpointTensor E F n) : z ∈ S := by
    apply endpointWord_mem_closed_submodule S (f - g).isClosed_ker ?_ z
    intro d x
    exact sub_eq_zero.mpr (hword d x)
  ext z
  exact sub_eq_zero.mp (hmem z)

/-- Vanishing matrix coefficients on all endpoint words force the operator to vanish. -/
theorem endpointOperator_eq_zero_of_word_coefficients {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (hword : ∀ d x c z, inner ℂ (endpointWord c z) (Y (endpointWord d x)) = 0) : Y = 0 := by
  apply continuousLinearMap_ext_endpointWords
  intro d x
  have hlin : innerSL ℂ (Y (endpointWord d x)) = 0 := by
    apply continuousLinearMap_ext_endpointWords
    intro c z
    change inner ℂ (Y (endpointWord d x)) (endpointWord c z) = 0
    simpa only [inner_conj_symm, map_zero] using
      congrArg (starRingEnd ℂ) (hword d x c z)
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have heq := congrArg (fun g : EndpointTensor E F l →L[ℂ] ℂ =>
    g (Y (endpointWord d x))) hlin
  change inner ℂ (Y (endpointWord d x)) (Y (endpointWord d x)) = 0 at heq
  exact heq

variable {E' F' : Type*}
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- The completed tensor product of an endpoint map and a bounded tail operator. -/
def endpointTensorMap {k l : ℕ} (p : E →L[ℂ] E')
    (A : CompletedTensorWord F k →L[ℂ] CompletedTensorWord F' l) :
    EndpointTensor E F k →L[ℂ] EndpointTensor E' F' l :=
  (TensorProduct.mapL p A).completion

@[simp] theorem endpointTensorMap_insert {k l : ℕ} (p : E →L[ℂ] E')
    (A : CompletedTensorWord F k →L[ℂ] CompletedTensorWord F' l)
    (d : E) (x : CompletedTensorWord F k) :
    endpointTensorMap p A (endpointInsert d x) = endpointInsert (p d) (A x) := by
  change (TensorProduct.mapL p A).completion
      ((d ⊗ₜ[ℂ] x : E ⊗[ℂ] CompletedTensorWord F k) :
        UniformSpace.Completion (E ⊗[ℂ] CompletedTensorWord F k)) =
    ((p d ⊗ₜ[ℂ] A x : E' ⊗[ℂ] CompletedTensorWord F' l) :
      UniformSpace.Completion (E' ⊗[ℂ] CompletedTensorWord F' l))
  rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]

/-- The actual operator `I_E ⊗ A` on completed endpoint tensors. -/
def endpointAmplification {k l : ℕ}
    (A : CompletedTensorWord F k →L[ℂ] CompletedTensorWord F l) :
    EndpointTensor E F k →L[ℂ] EndpointTensor E F l :=
  endpointTensorMap (ContinuousLinearMap.id ℂ E) A

@[simp] theorem endpointAmplification_insert {k l : ℕ}
    (A : CompletedTensorWord F k →L[ℂ] CompletedTensorWord F l)
    (d : E) (x : CompletedTensorWord F k) :
    endpointAmplification A (endpointInsert d x) = endpointInsert d (A x) := by
  exact endpointTensorMap_insert (ContinuousLinearMap.id ℂ E) A d x

/-- Contracting the endpoint is adjoint to inserting that endpoint. -/
theorem inner_tensorSlice_endpointInsert {n : ℕ} (d : E)
    (x : CompletedTensorWord F n) (z : EndpointTensor E F n) :
    inner ℂ x (tensorSlice d z) = inner ℂ (endpointInsert d x) z := by
  unfold EndpointTensor HilbertTensor at *
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change inner ℂ x (tensorSlice d (endpointInsert a b)) =
        inner ℂ (endpointInsert d x) (endpointInsert a b)
      have hs : tensorSlice d (endpointInsert a b) = inner ℂ d a • b :=
        (tensorSlice_coe d (a ⊗ₜ[ℂ] b)).trans (algebraTensorSlice_tmul d a b)
      rw [hs, inner_smul_right, inner_endpointInsert]
    | add a b ha hb =>
      change inner ℂ x (tensorSlice d ((a + b : E ⊗[ℂ] CompletedTensorWord F n) :
          HilbertTensor E (CompletedTensorWord F n))) =
        inner ℂ (endpointInsert d x) ((a + b : E ⊗[ℂ] CompletedTensorWord F n) :
          HilbertTensor E (CompletedTensorWord F n))
      have hs : tensorSlice d ((a + b : E ⊗[ℂ] CompletedTensorWord F n) :
          HilbertTensor E (CompletedTensorWord F n)) =
          tensorSlice d (a : HilbertTensor E (CompletedTensorWord F n)) +
            tensorSlice d (b : HilbertTensor E (CompletedTensorWord F n)) :=
        (congrArg (tensorSlice d) (hilbertTensor_coe_add a b)).trans
          ((tensorSlice d).map_add _ _)
      calc
        _ = inner ℂ x (tensorSlice d (a : HilbertTensor E (CompletedTensorWord F n)) +
              tensorSlice d (b : HilbertTensor E (CompletedTensorWord F n))) :=
          congrArg (fun y => inner ℂ x y) hs
        _ = inner ℂ x (tensorSlice d (a : HilbertTensor E (CompletedTensorWord F n))) +
              inner ℂ x (tensorSlice d (b : HilbertTensor E (CompletedTensorWord F n))) :=
          inner_add_right _ _ _
        _ = inner ℂ (endpointInsert d x) (a : HilbertTensor E (CompletedTensorWord F n)) +
              inner ℂ (endpointInsert d x) (b : HilbertTensor E (CompletedTensorWord F n)) :=
          congrArg₂ (· + ·) ha hb
        _ = _ := (congrArg (fun y => inner ℂ (endpointInsert d x) y)
            (hilbertTensor_coe_add a b)).trans (inner_add_right _ _ _) |>.symm

/-- Compress the endpoint of a bounded operator to the chosen trace vector. -/
def endpointCompression {k l : ℕ} (Ω : E)
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) :
    CompletedTensorWord F k →L[ℂ] CompletedTensorWord F l :=
  (tensorSlice Ω).comp (Y.comp (endpointInsert Ω))

@[simp] theorem endpointCompression_coefficient {k l : ℕ} (Ω : E)
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (x : Fin k → F) (z : Fin l → F) :
    inner ℂ (completedTensorWord z) (endpointCompression Ω Y (completedTensorWord x)) =
      inner ℂ (endpointWord Ω z) (Y (endpointWord Ω x)) := by
  simp only [endpointCompression, ContinuousLinearMap.comp_apply,
    inner_tensorSlice_endpointInsert, endpointWord]

/-- Coefficient factorization reconstructs `I_E ⊗ A` using proved totality. -/
theorem endpointOperator_eq_amplification {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (A : CompletedTensorWord F k →L[ℂ] CompletedTensorWord F l)
    (hcoeff : ∀ d x c z, inner ℂ (endpointWord c z) (Y (endpointWord d x)) =
      inner ℂ c d * inner ℂ (completedTensorWord z) (A (completedTensorWord x))) :
    Y = endpointAmplification A := by
  apply sub_eq_zero.mp
  apply endpointOperator_eq_zero_of_word_coefficients
  intro d x c z
  change inner ℂ (endpointWord c z)
    (Y (endpointWord d x) - endpointAmplification A (endpointWord d x)) = 0
  rw [inner_sub_right, hcoeff]
  simp only [endpointWord, endpointAmplification_insert, inner_endpointInsert, sub_self]

/-- A bounded operator acting only on the unrestricted endpoint. -/
def endpointHeadAction {n : ℕ} (p : E →L[ℂ] E) :
    EndpointTensor E F n →L[ℂ] EndpointTensor E F n :=
  endpointTensorMap p (ContinuousLinearMap.id ℂ (CompletedTensorWord F n))

@[simp] theorem endpointHeadAction_insert {n : ℕ} (p : E →L[ℂ] E)
    (d : E) (x : CompletedTensorWord F n) :
    endpointHeadAction p (endpointInsert d x) = endpointInsert (p d) x :=
  endpointTensorMap_insert p (ContinuousLinearMap.id ℂ _) d x

variable [CompleteSpace E]

/-- Moving an endpoint action across an inner product requires only the
ordinary Hilbert adjoint law. -/
theorem inner_endpointHeadAction {n : ℕ} (p : E →L[ℂ] E)
    (c : E) (z : CompletedTensorWord F n) (w : EndpointTensor E F n) :
    inner ℂ (endpointInsert c z) (endpointHeadAction p w) =
      inner ℂ (endpointInsert (p.adjoint c) z) w := by
  have heq := continuousLinearMap_ext_endpointWords
    ((innerSL ℂ (endpointInsert c z)).comp (endpointHeadAction p))
    (innerSL ℂ (endpointInsert (p.adjoint c) z)) (fun d x => by
      change inner ℂ (endpointInsert c z)
        (endpointHeadAction p (endpointInsert d (completedTensorWord x))) =
          inner ℂ (endpointInsert (p.adjoint c) z) (endpointInsert d (completedTensorWord x))
      rw [endpointHeadAction_insert, inner_endpointInsert, inner_endpointInsert,
        p.adjoint_inner_left])
  exact congrArg (fun L : EndpointTensor E F n →L[ℂ] ℂ => L w) heq

/-- Left intertwining moves arbitrary first endpoints to the trace-vector
coefficient. This is the algebraic replacement for a separate commutant theorem. -/
theorem endpoint_coefficient_transfer {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) (p : E →L[ℂ] E)
    (hY : Y.comp (endpointHeadAction (n := k) p) =
      (endpointHeadAction (n := l) p).comp Y)
    (Ω c : E) (x : Fin k → F) (z : Fin l → F) :
    inner ℂ (endpointWord c z) (Y (endpointWord (p Ω) x)) =
      inner ℂ (endpointWord (p.adjoint c) z) (Y (endpointWord Ω x)) := by
  have heq := congrArg (fun L : EndpointTensor E F k →L[ℂ] EndpointTensor E F l =>
    L (endpointWord Ω x)) hY
  simp only [ContinuousLinearMap.comp_apply, endpointWord, endpointHeadAction_insert] at heq
  change inner ℂ (endpointInsert c (completedTensorWord z))
    (Y (endpointInsert (p Ω) (completedTensorWord x))) = _
  rw [heq, inner_endpointHeadAction]
  rfl

omit [CompleteSpace E] in
/-- An endpoint and `n` matrix-unit tail letters contribute `n + 1` normalized
Hilbert--Schmidt factors, even when endpoint and tail spaces differ. -/
theorem norm_endpointWord_le_matrix_units {n : ℕ} (d : E) (x : Fin n → F)
    (m : ℝ) (hm : 0 < m) (hd : ‖d‖ ≤ m ^ (-(1 : ℝ) / 2))
    (hx : ∀ i, ‖x i‖ ≤ m ^ (-(1 : ℝ) / 2)) :
    ‖endpointWord d x‖ ≤ m ^ (-((n : ℝ) + 1) / 2) := by
  rw [endpointWord, norm_endpointInsert]
  calc
    _ ≤ m ^ (-(1 : ℝ) / 2) * m ^ (-(n : ℝ) / 2) :=
      mul_le_mul hd (norm_completedTensorWord_le_matrix_units x m hm hx)
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hm]
      congr 1
      ring

end KadisonSimilarity

end

end OAI
