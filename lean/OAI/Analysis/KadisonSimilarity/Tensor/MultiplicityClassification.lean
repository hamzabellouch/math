import OAI.Analysis.KadisonSimilarity.Tensor.EndpointClassification

namespace OAI

/-!
# Hilbert multiplicities in the invariant-intertwiner theorem

Scalar matrix coefficients in the multiplicity Hilbert space are genuine
bounded endpoint intertwiners. Tensor totality reconstructs the full operator
from these slices. Repeated-letter compressions provide the bounded operator
on the multiplicity space used in propagation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {G H K L : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

/-- Insert the first tensor coordinate in a completed Hilbert tensor product. -/
def hilbertTensorInsert (a : G) : H →L[ℂ] HilbertTensor G H :=
  UniformSpace.Completion.toComplL.comp (TensorProduct.mkL ℂ G H a)

@[simp] theorem hilbertTensorInsert_apply (a : G) (x : H) :
    hilbertTensorInsert a x = (a ⊗ₜ[ℂ] x : G ⊗[ℂ] H) := rfl

@[simp] theorem norm_hilbertTensorInsert (a : G) (x : H) :
    ‖hilbertTensorInsert a x‖ = ‖a‖ * ‖x‖ := by
  exact (UniformSpace.Completion.norm_coe (a ⊗ₜ[ℂ] x)).trans
    (TensorProduct.norm_tmul a x)

@[simp] theorem inner_hilbertTensorInsert (a b : G) (x y : H) :
    inner ℂ (hilbertTensorInsert a x) (hilbertTensorInsert b y) =
      inner ℂ a b * inner ℂ x y := by
  exact (UniformSpace.Completion.inner_coe (a ⊗ₜ[ℂ] x) (b ⊗ₜ[ℂ] y)).trans
    (TensorProduct.inner_tmul ℂ a b x y)

/-- Totality of completed elementary Hilbert tensors. -/
theorem continuousLinearMap_ext_hilbertTensorInsert
    (f g : HilbertTensor G H →L[ℂ] L)
    (h : ∀ a x, f (hilbertTensorInsert a x) = g (hilbertTensorInsert a x)) : f = g := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq f.continuous g.continuous
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul a x => exact h a x
    | add x y hx hy =>
      change f ((x + y : G ⊗[ℂ] H) : HilbertTensor G H) =
        g ((x + y : G ⊗[ℂ] H) : HilbertTensor G H)
      calc
        _ = f (x : HilbertTensor G H) + f (y : HilbertTensor G H) :=
          (congrArg f (hilbertTensor_coe_add x y)).trans (f.map_add _ _)
        _ = g (x : HilbertTensor G H) + g (y : HilbertTensor G H) :=
          congrArg₂ (· + ·) hx hy
        _ = _ := ((congrArg g (hilbertTensor_coe_add x y)).trans (g.map_add _ _)).symm

/-- The lift of an operator leaving the first tensor coordinate unchanged. -/
def hilbertTensorLift (T : H →L[ℂ] K) : HilbertTensor G H →L[ℂ] HilbertTensor G K :=
  (TensorProduct.mapL (ContinuousLinearMap.id ℂ G) T).completion

@[simp] theorem hilbertTensorLift_insert (T : H →L[ℂ] K) (a : G) (x : H) :
    hilbertTensorLift T (hilbertTensorInsert a x) = hilbertTensorInsert a (T x) := by
  change (TensorProduct.mapL (ContinuousLinearMap.id ℂ G) T).completion
      ((a ⊗ₜ[ℂ] x : G ⊗[ℂ] H) : UniformSpace.Completion (G ⊗[ℂ] H)) =
    ((a ⊗ₜ[ℂ] T x : G ⊗[ℂ] K) : UniformSpace.Completion (G ⊗[ℂ] K))
  simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
    ContinuousLinearMap.id_apply]

variable [CompleteSpace H] [CompleteSpace K]

@[simp] theorem tensorSlice_insert (a b : G) (x : H) :
    tensorSlice b (hilbertTensorInsert a x) = inner ℂ b a • x := by
  simp only [hilbertTensorInsert_apply, tensorSlice_coe, algebraTensorSlice_tmul]

/-- A scalar matrix coefficient in the multiplicity space. -/
def multiplicitySlice (Y : HilbertTensor G H →L[ℂ] HilbertTensor G K) (a b : G) : H →L[ℂ] K :=
  (tensorSlice b).comp (Y.comp (hilbertTensorInsert a))

theorem tensorSlice_lift (T : H →L[ℂ] K) (b : G) :
    (tensorSlice b).comp (hilbertTensorLift T) = T.comp (tensorSlice b) := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  simp only [ContinuousLinearMap.comp_apply, hilbertTensorLift_insert, tensorSlice_insert, map_smul]

omit [CompleteSpace H] in
/-- Lifted intertwining implies the scalar slice intertwining. -/
theorem multiplicitySlice_intertwines
    (Y : HilbertTensor G H →L[ℂ] HilbertTensor G K)
    (S : H →L[ℂ] H) (T : K →L[ℂ] K)
    (hY : Y.comp (hilbertTensorLift S) = (hilbertTensorLift T).comp Y) (a b : G) :
    (multiplicitySlice Y a b).comp S = T.comp (multiplicitySlice Y a b) := by
  ext x
  have heq := congrArg (fun A : HilbertTensor G H →L[ℂ] HilbertTensor G K =>
    A (hilbertTensorInsert a x)) hY
  simp only [ContinuousLinearMap.comp_apply, hilbertTensorLift_insert] at heq
  change tensorSlice b (Y (hilbertTensorInsert a (S x))) =
    T (tensorSlice b (Y (hilbertTensorInsert a x)))
  rw [heq]
  exact congrArg (fun A : HilbertTensor G K →L[ℂ] K => A (Y (hilbertTensorInsert a x)))
    (tensorSlice_lift T b)

omit [CompleteSpace H] in
/-- Inner products with elementary tensors are exactly multiplicity slices. -/
theorem inner_multiplicitySlice (Y : HilbertTensor G H →L[ℂ] HilbertTensor G K)
    (a b : G) (x : H) (z : K) :
    inner ℂ z (multiplicitySlice Y a b x) =
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
      have hs : tensorSlice b ((u + v : G ⊗[ℂ] K) : HilbertTensor G K) =
          tensorSlice b (u : HilbertTensor G K) + tensorSlice b (v : HilbertTensor G K) :=
        (congrArg (tensorSlice b) (hilbertTensor_coe_add u v)).trans
          ((tensorSlice b).map_add _ _)
      calc
        _ = inner ℂ z (tensorSlice b (u : HilbertTensor G K) +
              tensorSlice b (v : HilbertTensor G K)) := congrArg (fun y => inner ℂ z y) hs
        _ = inner ℂ z (tensorSlice b (u : HilbertTensor G K)) +
              inner ℂ z (tensorSlice b (v : HilbertTensor G K)) := inner_add_right _ _ _
        _ = inner ℂ (hilbertTensorInsert b z) (u : HilbertTensor G K) +
              inner ℂ (hilbertTensorInsert b z) (v : HilbertTensor G K) := congrArg₂ (· + ·) hu hv
        _ = _ := ((congrArg (fun y => inner ℂ (hilbertTensorInsert b z) y)
            (hilbertTensor_coe_add u v)).trans (inner_add_right _ _ _)).symm

omit [CompleteSpace H] in
/-- All scalar multiplicity slices determine the full bounded operator. -/
theorem multiplicitySlice_ext (Y Z : HilbertTensor G H →L[ℂ] HilbertTensor G K)
    (hslice : ∀ a b, multiplicitySlice Y a b = multiplicitySlice Z a b) : Y = Z := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  have hcoef (b : G) (z : K) :
      inner ℂ (hilbertTensorInsert b z) (Y (hilbertTensorInsert a x)) =
        inner ℂ (hilbertTensorInsert b z) (Z (hilbertTensorInsert a x)) := by
    rw [← inner_multiplicitySlice, ← inner_multiplicitySlice, hslice]
  have hlinear : innerSL ℂ (Y (hilbertTensorInsert a x)) =
      innerSL ℂ (Z (hilbertTensorInsert a x)) := by
    apply continuousLinearMap_ext_hilbertTensorInsert
    intro b z
    change inner ℂ (Y (hilbertTensorInsert a x)) (hilbertTensorInsert b z) =
      inner ℂ (Z (hilbertTensorInsert a x)) (hilbertTensorInsert b z)
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (hcoef b z)
  apply ext_inner_right ℂ
  intro v
  exact congrArg (fun A : HilbertTensor G K →L[ℂ] ℂ => A v) hlinear

omit [CompleteSpace H] in
@[simp] theorem multiplicitySlice_zero (a b : G) :
    multiplicitySlice (0 : HilbertTensor G H →L[ℂ] HilbertTensor G K) a b = 0 := by
  ext x
  simp [multiplicitySlice]

omit [CompleteSpace H] in
/-- Elementary tensor coefficients separate vectors in the completed product. -/
theorem hilbertTensor_ext_inner_insert (z w : HilbertTensor G H)
    (h : ∀ a x, inner ℂ (hilbertTensorInsert a x) z =
      inner ℂ (hilbertTensorInsert a x) w) : z = w := by
  have heq : innerSL ℂ z = innerSL ℂ w := by
    apply continuousLinearMap_ext_hilbertTensorInsert
    intro a x
    change inner ℂ z (hilbertTensorInsert a x) = inner ℂ w (hilbertTensorInsert a x)
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (h a x)
  apply ext_inner_right ℂ
  intro v
  exact congrArg (fun A : HilbertTensor G H →L[ℂ] ℂ => A v) heq

/-- Insert a fixed second tensor vector, leaving the multiplicity variable free. -/
def hilbertTensorRightInsert (w : H) : G →L[ℂ] HilbertTensor G H :=
  UniformSpace.Completion.toComplL.comp ((TensorProduct.mkL ℂ G H).flip w)

omit [CompleteSpace H] in
@[simp] theorem hilbertTensorRightInsert_apply (w : H) (a : G) :
    hilbertTensorRightInsert w a = hilbertTensorInsert a w := rfl

omit [CompleteSpace H] in
theorem norm_hilbertTensorRightInsert_le (w : H) :
    ‖hilbertTensorRightInsert (G := G) w‖ ≤ ‖w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  rw [hilbertTensorRightInsert_apply, norm_hilbertTensorInsert, mul_comm]

variable [CompleteSpace G]

/-- Compression to a chosen unit vector in the non-multiplicity factor. -/
def multiplicityCompression (Y : HilbertTensor G H →L[ℂ] HilbertTensor G H) (w : H) : G →L[ℂ] G :=
  (hilbertTensorRightInsert w).adjoint.comp (Y.comp (hilbertTensorRightInsert w))

omit [CompleteSpace H] in
theorem norm_multiplicityCompression_le
    (Y : HilbertTensor G H →L[ℂ] HilbertTensor G H) (w : H) (hw : ‖w‖ = 1) :
    ‖multiplicityCompression Y w‖ ≤ ‖Y‖ := by
  have hi : ‖hilbertTensorRightInsert (G := G) w‖ ≤ 1 := by
    simpa only [hw] using norm_hilbertTensorRightInsert_le (G := G) w
  calc
    _ ≤ ‖(hilbertTensorRightInsert (G := G) w).adjoint‖ *
        (‖Y‖ * ‖hilbertTensorRightInsert (G := G) w‖) :=
      le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = ‖hilbertTensorRightInsert (G := G) w‖ *
        (‖Y‖ * ‖hilbertTensorRightInsert (G := G) w‖) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * (‖Y‖ * 1) := mul_le_mul hi
      (mul_le_mul_of_nonneg_left hi (norm_nonneg Y)) (by positivity) (by positivity)
    _ = ‖Y‖ := by ring

theorem inner_multiplicityCompression
    (Y : HilbertTensor G H →L[ℂ] HilbertTensor G H) (w : H) (a b : G) :
    inner ℂ b (multiplicityCompression Y w a) =
      inner ℂ w (multiplicitySlice Y a b w) := by
  change inner ℂ b ((hilbertTensorRightInsert w).adjoint
    (Y (hilbertTensorRightInsert w a))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, hilbertTensorRightInsert_apply,
    hilbertTensorRightInsert_apply, inner_multiplicitySlice]

section EndpointMultiplicity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

omit [CompleteSpace E] in
/-- A unit endpoint and unit repeated letter give a unit vector at every level. -/
theorem norm_endpointWord_constant {n : ℕ} (Ω : E) (r : F)
    (hΩ : ‖Ω‖ = 1) (hr : ‖r‖ = 1) :
    ‖endpointWord Ω (fun _ : Fin n => r)‖ = 1 := by
  simp only [endpointWord, norm_endpointInsert, norm_completedTensorWord, hΩ, hr,
    Finset.prod_const_one, mul_one]

omit [CompleteSpace E] in
/-- Slice permutation formulas give one bounded multiplicity operator that
acts on every repeated-letter word. Its definition uses a single unit reference
word, but the conclusion holds for all letters, with no dependence on that word. -/
theorem exists_repeated_operator_of_slice_permutations {n : ℕ}
    (Y : HilbertTensor G (EndpointTensor E F n) →L[ℂ]
      HilbertTensor G (EndpointTensor E F n))
    (Ω : E) (hΩ : ‖Ω‖ = 1) (r₀ : F) (hr₀ : ‖r₀‖ = 1)
    (hslices : ∀ a b : G, ∃ c : PerfectMatching (Fin n ⊕ Fin n) → ℂ,
      multiplicitySlice Y a b = endpointAmplification (crossPairingOperator c)) :
    ∃ B : G →L[ℂ] G, ‖B‖ ≤ ‖Y‖ ∧ ∀ a d r,
      Y (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r))) =
        hilbertTensorInsert (B a) (endpointWord d (fun _ : Fin n => r)) := by
  classical
  let w₀ := endpointWord Ω (fun _ : Fin n => r₀)
  have hw₀ : ‖w₀‖ = 1 := norm_endpointWord_constant Ω r₀ hΩ hr₀
  let B := multiplicityCompression Y w₀
  refine ⟨B, norm_multiplicityCompression_le Y w₀ hw₀, ?_⟩
  intro a d r
  apply hilbertTensor_ext_inner_insert
  intro b z
  obtain ⟨c, hc⟩ := hslices a b
  let coefficient := ∑ P : {P : PerfectMatching (Fin n ⊕ Fin n) // IsCrossPairing P.1}, c P.1
  have hact (d : E) (r : F) :
      multiplicitySlice Y a b (endpointWord d (fun _ : Fin n => r)) =
        coefficient • endpointWord d (fun _ : Fin n => r) := by
    simp only [hc, endpointWord, endpointAmplification_insert,
      crossPairingOperator_constant, map_smul, coefficient]
  have hscalar : inner ℂ b (B a) = coefficient := by
    rw [inner_multiplicityCompression]
    change inner ℂ w₀ (multiplicitySlice Y a b
      (endpointWord Ω (fun _ : Fin n => r₀))) = coefficient
    rw [hact, inner_smul_right, inner_self_eq_norm_sq_to_K, hw₀]
    simp
  rw [← inner_multiplicitySlice, hact, inner_smul_right, inner_hilbertTensorInsert, hscalar]

omit [CompleteSpace E] in
/-- The compression along any unit repeated tail recovers the same multiplicity
operator. This gives explicit independence of the reference tail. -/
theorem multiplicityCompression_eq_of_repeated_action {n : ℕ}
    (Y : HilbertTensor G (EndpointTensor E F n) →L[ℂ]
      HilbertTensor G (EndpointTensor E F n)) (B : G →L[ℂ] G)
    (hact : ∀ a d r, Y (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r))) =
      hilbertTensorInsert (B a) (endpointWord d (fun _ : Fin n => r)))
    (Ω : E) (hΩ : ‖Ω‖ = 1) (r : F) (hr : ‖r‖ = 1) :
    multiplicityCompression Y (endpointWord Ω (fun _ : Fin n => r)) = B := by
  ext a
  apply ext_inner_left ℂ
  intro b
  rw [inner_multiplicityCompression, inner_multiplicitySlice, hact, inner_hilbertTensorInsert,
    inner_self_eq_norm_sq_to_K, norm_endpointWord_constant Ω r hΩ hr]
  simp

variable {α : Type*} [Fintype α] [DecidableEq α] {k l : ℕ}

/-- Word covariance before taking scalar multiplicity slices. -/
structure MultiplicityMatrixCovariance
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : HilbertTensor G (EndpointTensor E F k) →L[ℂ]
      HilbertTensor G (EndpointTensor E F l)) where
  sourceAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F k →ₗᵢ[ℂ] EndpointTensor E F k
  testAction : Matrix.unitaryGroup α ℂ → EndpointTensor E F l →ₗᵢ[ℂ] EndpointTensor E F l
  intertwine : ∀ u, Y.comp (hilbertTensorLift (sourceAction u).toContinuousLinearMap) =
    (hilbertTensorLift (testAction u).toContinuousLinearMap).comp Y
  source_covariance : ∀ (u : Matrix.unitaryGroup α ℂ)
      (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord Ω (fun i => R.center ((u : Matrix α α ℂ) * v (some (Sum.inl i)) * star (u : Matrix α α ℂ))) =
      sourceAction u (endpointWord Ω (fun i => R.center (v (some (Sum.inl i)))))
  test_covariance : ∀ (u : Matrix.unitaryGroup α ℂ)
      (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ),
    endpointWord (R.full (star ((u : Matrix α α ℂ) * v none * star (u : Matrix α α ℂ))))
      (fun j => J (R.center ((u : Matrix α α ℂ) * v (some (Sum.inr j)) * star (u : Matrix α α ℂ)))) =
      testAction u (endpointWord (R.full (star (v none)))
        (fun j => J (R.center (v (some (Sum.inr j))))))

/-- Taking a scalar multiplicity coefficient preserves actual word covariance. -/
def MultiplicityMatrixCovariance.slice
    {R : MatrixHilbertStage (E := E) (F := F) (α := α)} {J : F →ₗᵢ⋆[ℂ] F}
    {Ω : E} {Y : HilbertTensor G (EndpointTensor E F k) →L[ℂ]
      HilbertTensor G (EndpointTensor E F l)}
    (cov : MultiplicityMatrixCovariance R J Ω Y) (a b : G) :
    MatrixWordCovariance R J Ω (multiplicitySlice Y a b) where
  sourceAction := cov.sourceAction
  testAction := cov.testAction
  intertwine u := multiplicitySlice_intertwines Y _ _ (cov.intertwine u) a b
  source_covariance := cov.source_covariance
  test_covariance := cov.test_covariance

variable {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

omit [CompleteSpace G] in
/-- All unequal-level blocks vanish, including their Hilbert multiplicities. -/
theorem multiplicity_intertwiner_zero_of_schurWeyl
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : HilbertTensor G (EndpointTensor E F k) →L[ℂ]
      HilbertTensor G (EndpointTensor E F l))
    (hleft : ∀ s a, Y.comp (hilbertTensorLift (endpointHeadAction (n := k) ((T.stage s).left a))) =
      (hilbertTensorLift (endpointHeadAction (n := l) ((T.stage s).left a))).comp Y)
    (cov : ∀ s, MultiplicityMatrixCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) (hkl : k ≠ l) : Y = 0 := by
  apply multiplicitySlice_ext
  intro a b
  rw [multiplicitySlice_zero]
  exact endpoint_intertwiner_zero_of_schurWeyl T (multiplicitySlice Y a b)
    (fun s c => multiplicitySlice_intertwines Y _ _ (hleft s c) a b)
    (fun s => (cov s).slice a b) spanning hcontraction labels hlabels hkl

/-- On equal levels a bounded operator on the multiplicity factor acts on
all repeated-letter words, independently of the unit repeated letter. -/
theorem exists_multiplicity_repeated_operator_of_schurWeyl {n : ℕ}
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (Y : HilbertTensor G (EndpointTensor E F n) →L[ℂ]
      HilbertTensor G (EndpointTensor E F n))
    (hleft : ∀ s a, Y.comp (hilbertTensorLift (endpointHeadAction (n := n) ((T.stage s).left a))) =
      (hilbertTensorLift (endpointHeadAction (n := n) ((T.stage s).left a))).comp Y)
    (cov : ∀ s, MultiplicityMatrixCovariance (T.stage s) T.conjugation T.traceVector Y)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin n ⊕ Fin n)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin n ⊕ Fin n))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin n ⊕ Fin n) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) :
    ∃ B : G →L[ℂ] G, ‖B‖ ≤ ‖Y‖ ∧ ∀ a d r,
      Y (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r))) =
        hilbertTensorInsert (B a) (endpointWord d (fun _ : Fin n => r)) := by
  apply exists_repeated_operator_of_slice_permutations Y T.traceVector T.norm_traceVector
    (T.realOrthonormal 0) (T.realOrthonormal_orthonormal.norm_eq_one 0)
  intro a b
  exact endpoint_intertwiner_permutations_of_schurWeyl T (multiplicitySlice Y a b)
    (fun s c => multiplicitySlice_intertwines Y _ _ (hleft s c) a b)
    (fun s => (cov s).slice a b) spanning hcontraction labels hlabels

end EndpointMultiplicity

end KadisonSimilarity

end

end OAI
