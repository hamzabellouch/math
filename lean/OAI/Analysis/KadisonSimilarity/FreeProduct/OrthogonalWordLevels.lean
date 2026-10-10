import OAI.Analysis.KadisonSimilarity.FreeProduct.WordLevelClassification

namespace OAI

/-! Orthogonal word-level inclusions turn the proved off-diagonal block
vanishing into actual preservation of each full word level. -/

noncomputable section
namespace KadisonSimilarity

variable {W : ℕ → Type*} [∀ n, NormedAddCommGroup (W n)]
  [∀ n, InnerProductSpace ℂ (W n)] [∀ n, CompleteSpace (W n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual isometric word inclusions with orthogonal ranges and dense linear
span. No operator invariance is built into these geometric data. -/
structure OrthogonalWordLevels (W : ℕ → Type*) [∀ n, NormedAddCommGroup (W n)]
    [∀ n, InnerProductSpace ℂ (W n)] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  inclusion : ∀ n, W n →ₗᵢ[ℂ] H
  orthogonal : ∀ n m, n ≠ m → ∀ x y, inner ℂ (inclusion n x) (inclusion m y) = 0
  dense_span : (Submodule.span ℂ (⋃ n, Set.range (inclusion n))).topologicalClosure = ⊤

namespace OrthogonalWordLevels

variable (U : OrthogonalWordLevels W H)

def coordinate (n : ℕ) : H →L[ℂ] W n := (U.inclusion n).toContinuousLinearMap.adjoint

def block (Y : H →L[ℂ] H) (m n : ℕ) : W n →L[ℂ] W m :=
  (U.coordinate m).comp (Y.comp (U.inclusion n).toContinuousLinearMap)

/-- Orthogonal word-block compression does not increase operator norm. -/
theorem norm_block_le (Y : H →L[ℂ] H) (m n : ℕ) : ‖U.block Y m n‖ ≤ ‖Y‖ := by
  have hi (j : ℕ) : ‖(U.inclusion j).toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖U.inclusion j x‖ ≤ 1 * ‖x‖
    rw [(U.inclusion j).norm_map, one_mul]
  have hc : ‖U.coordinate m‖ ≤ 1 := by
    change ‖(U.inclusion m).toContinuousLinearMap.adjoint‖ ≤ 1
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hi m
  calc
    ‖U.block Y m n‖ ≤ ‖U.coordinate m‖ *
        (‖Y‖ * ‖(U.inclusion n).toContinuousLinearMap‖) :=
      le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖Y‖ * 1) := mul_le_mul hc
      (mul_le_mul_of_nonneg_left (hi n) (norm_nonneg Y)) (by positivity) (by positivity)
    _ = ‖Y‖ := by ring

@[simp] theorem coordinate_inclusion_self (n : ℕ) (x : W n) :
    U.coordinate n (U.inclusion n x) = x := by
  exact congrArg (fun T : W n →L[ℂ] W n => T x) (U.inclusion n).adjoint_comp_self

theorem coordinate_inclusion_ne {n m : ℕ} (h : n ≠ m) (x : W m) :
    U.coordinate n (U.inclusion m x) = 0 := by
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((U.inclusion n).toContinuousLinearMap.adjoint (U.inclusion m x)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
  exact U.orthogonal n m h y x

omit [∀ n, CompleteSpace (W n)] [CompleteSpace H] in
/-- A continuous linear map is determined by its values on the actual word
inclusions because their linear span is dense. -/
theorem map_eq_zero_of_levels {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (f : H →L[ℂ] K) (hf : ∀ n x, f (U.inclusion n x) = 0) : f = 0 := by
  have hs : Submodule.span ℂ (⋃ n, Set.range (U.inclusion n)) ≤ f.ker := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨n, y, rfl⟩ := Set.mem_iUnion.mp hx
    exact hf n y
  have ht := (Submodule.span ℂ (⋃ n, Set.range (U.inclusion n))).topologicalClosure_minimal
    hs f.isClosed_ker
  rw [U.dense_span] at ht
  ext x
  exact ht (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ H))

/-- All word-level coordinates separate vectors in the ambient Hilbert space. -/
theorem eq_zero_of_coordinates (z : H) (hz : ∀ n, U.coordinate n z = 0) : z = 0 := by
  have hf : innerSL ℂ z = 0 := U.map_eq_zero_of_levels (innerSL ℂ z) (by
    intro n x
    apply inner_eq_zero_symm.mp
    change inner ℂ ((U.inclusion n).toContinuousLinearMap x) z = 0
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ x (U.coordinate n z) = 0
    rw [hz, inner_zero_right])
  exact inner_self_eq_zero.mp (congrArg (fun f : H →L[ℂ] ℂ => f z) hf)

/-- Compressing a global commutation identity yields the actual block
intertwining. Adjoint covariance of the target inclusion supplies its coordinate
covariance. -/
theorem block_intertwines (Y A : H →L[ℂ] H) {n m : ℕ}
    (S : W n →L[ℂ] W n) (T : W m →L[ℂ] W m)
    (hY : Y.comp A = A.comp Y)
    (hsource : A.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp S)
    (htarget : A.adjoint.comp (U.inclusion m).toContinuousLinearMap =
      (U.inclusion m).toContinuousLinearMap.comp T.adjoint) :
    (U.block Y m n).comp S = T.comp (U.block Y m n) := by
  have hc := congrArg ContinuousLinearMap.adjoint htarget
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] at hc
  ext x
  have hs := congrArg (fun C : W n →L[ℂ] H => C x) hsource
  have hy := congrArg (fun C : H →L[ℂ] H => C (U.inclusion n x)) hY
  have ht := congrArg (fun C : H →L[ℂ] W m => C (Y (U.inclusion n x))) hc
  simp only [ContinuousLinearMap.comp_apply] at hs hy ht
  change A (U.inclusion n x) = U.inclusion n (S x) at hs
  change U.coordinate m (Y (U.inclusion n (S x))) = T (U.coordinate m (Y (U.inclusion n x)))
  rw [← hs, hy]
  exact ht

/-- Vanishing of the off-diagonal blocks implies actual preservation of every
word level; this uses dense span, rather than an assumed direct-sum model. -/
theorem preserves_of_offDiagonal_zero (Y : H →L[ℂ] H)
    (hzero : ∀ m n, m ≠ n → U.block Y m n = 0) (n : ℕ) :
    Y.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n) := by
  ext x
  change Y (U.inclusion n x) = U.inclusion n (U.block Y n n x)
  apply sub_eq_zero.mp
  apply U.eq_zero_of_coordinates
  intro m
  rw [map_sub]
  by_cases hmn : m = n
  · subst m
    rw [U.coordinate_inclusion_self]
    exact sub_self _
  · rw [U.coordinate_inclusion_ne hmn, sub_zero]
    change U.block Y m n x = 0
    rw [hzero m n hmn]
    rfl

end OrthogonalWordLevels

section MatrixActions

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- The actual space of one word level, including its degree-dependent
multiplicity. -/
abbrev MultiplicityWordSpace (G : ℕ → Type*) [∀ n, NormedAddCommGroup (G n)]
    [∀ n, InnerProductSpace ℂ (G n)] (E F : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (n : ℕ) :=
  HilbertTensor (G n) (EndpointTensor E F n)

/-- Raw action data on the ambient word Hilbert space. Both ordinary and
adjoint inclusion covariance are explicit, as supplied by reducing free-word
levels. No operator block vanishing is included. -/
structure WordLevelMatrixActions
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H) where
  leftAction : ∀ s, Matrix (A s) (A s) ℂ → H →L[ℂ] H
  unitaryAction : ∀ s, Matrix.unitaryGroup (A s) ℂ → H →L[ℂ] H
  wordAction : ∀ s n, Matrix.unitaryGroup (A s) ℂ →
    EndpointTensor E F n →ₗᵢ[ℂ] EndpointTensor E F n
  left_inclusion : ∀ s a n, (leftAction s a).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (endpointHeadAction (n := n) ((T.stage s).left a)))
  left_adjoint_inclusion : ∀ s a n,
    (leftAction s a).adjoint.comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (endpointHeadAction (n := n) ((T.stage s).left a))).adjoint
  unitary_inclusion : ∀ s u n, (unitaryAction s u).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (wordAction s n u).toContinuousLinearMap)
  unitary_adjoint_inclusion : ∀ s u n,
    (unitaryAction s u).adjoint.comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (wordAction s n u).toContinuousLinearMap).adjoint
  source_word : ∀ s n (u : Matrix.unitaryGroup (A s) ℂ)
      (v : Fin n → Matrix (A s) (A s) ℂ),
    endpointWord T.traceVector (fun i => (T.stage s).center
      ((u : Matrix (A s) (A s) ℂ) * v i * star (u : Matrix (A s) (A s) ℂ))) =
      wordAction s n u (endpointWord T.traceVector (fun i => (T.stage s).center (v i)))
  test_word : ∀ s n (u : Matrix.unitaryGroup (A s) ℂ)
      (a : Matrix (A s) (A s) ℂ) (v : Fin n → Matrix (A s) (A s) ℂ),
    endpointWord ((T.stage s).full (star
      ((u : Matrix (A s) (A s) ℂ) * a * star (u : Matrix (A s) (A s) ℂ))))
      (fun i => T.conjugation ((T.stage s).center
        ((u : Matrix (A s) (A s) ℂ) * v i * star (u : Matrix (A s) (A s) ℂ)))) =
      wordAction s n u (endpointWord ((T.stage s).full (star a))
        (fun i => T.conjugation ((T.stage s).center (v i))))

variable (T : TracialMatrixTower (E := E) (F := F) (A := A))
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)
  (C : WordLevelMatrixActions T U) (Y : H →L[ℂ] H)
  (hleft : ∀ s a, Y.comp (C.leftAction s a) = (C.leftAction s a).comp Y)
  (hunitary : ∀ s u, Y.comp (C.unitaryAction s u) = (C.unitaryAction s u).comp Y)

/-- Ambient commutation and the actual inclusion identities supply the whole
cross-multiplicity covariance of every compressed word block. -/
def WordLevelMatrixActions.blockCovariance (s k l : ℕ) :
    CrossMultiplicityMatrixCovariance (T.stage s) T.conjugation T.traceVector (U.block Y l k) where
  sourceAction := C.wordAction s k
  testAction := C.wordAction s l
  intertwine u := U.block_intertwines Y (C.unitaryAction s u) _ _ (hunitary s u)
    (C.unitary_inclusion s u k) (C.unitary_adjoint_inclusion s u l)
  source_covariance u v := C.source_word s k u (fun i => v (some (.inl i)))
  test_covariance u v := C.test_word s l u (v none) (fun i => v (some (.inr i)))

include hleft hunitary in
/-- Global word-level preservation follows from Schur--Weyl and ambient
commutation. Off-diagonal block vanishing is proved, not supplied. -/
theorem word_levels_preserved_of_schurWeyl
    (spanning : ∀ k l s,
      SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (hcontraction : ∀ k l s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ k l s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ k l s, Function.Injective (labels k l s)) (n : ℕ) :
    Y.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n) := by
  apply U.preserves_of_offDiagonal_zero Y
  intro l k hkl
  exact crossMultiplicity_intertwiner_zero_of_schurWeyl T (U.block Y l k)
    (fun s a => U.block_intertwines Y (C.leftAction s a) _ _ (hleft s a)
      (C.left_inclusion s a k) (C.left_adjoint_inclusion s a l))
    (fun s => WordLevelMatrixActions.blockCovariance T U C Y hunitary s k l)
    (spanning k l) (hcontraction k l) (labels k l) (hlabels k l) (Ne.symm hkl)

end MatrixActions

end KadisonSimilarity

end

end OAI
