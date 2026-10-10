import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixRealization
import OAI.Analysis.KadisonSimilarity.Tensor.EndpointClassification

namespace OAI

/-!
# Tracial matrix towers from actual embedded matrix algebras

The matrix-stage geometry is constructed from nested trace-preserving matrix
embeddings in a tracial Hilbert representation. Density of centered trace-zero
stages is derived by orthogonal projection from density of the full stages.
-/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- Raw nested matrix embeddings, with density stated for their represented
algebra vectors. No Hilbert coefficient identity is part of this data. -/
structure NestedTracialMatrices (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) where
  embedding : ∀ s, Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] R
  trace_embedding : ∀ s a, τ (embedding s a) =
    (Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace a
  inclusion : ∀ s t, s ≤ t → Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] Matrix (A t) (A t) ℂ
  compatible : ∀ s t h a, embedding t (inclusion s t h a) = embedding s a
  dense : Dense (⋃ s, Set.range (fun a => V (embedding s a)))

/-- A real orthonormal sequence expressed entirely in the tracial algebra.
Its Hilbert realization is derived below. -/
structure RealTracialSequence (τ : R →ₗ[ℂ] ℂ) where
  vector : ℕ → R
  trace_zero : ∀ n, τ (vector n) = 0
  selfadjoint : ∀ n, star (vector n) = vector n
  inner : ∀ i j, τ (star (vector i) * vector j) = if i = j then 1 else 0

variable (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (M : NestedTracialMatrices (A := A) τ V)

include M in
omit [CompleteSpace E] [∀ s, Nonempty (A s)] in
/-- Density of the matrix union already implies density of the represented
algebra, so no separate cyclic-density assumption is needed by the tower. -/
theorem NestedTracialMatrices.denseRange_vector : DenseRange V := by
  apply M.dense.mono
  intro x hx
  obtain ⟨s, a, rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨M.embedding s a, rfl⟩

include M in
omit [CompleteSpace E] in
/-- A unital trace-preserving nonempty matrix stage normalizes the ambient
trace automatically. -/
theorem NestedTracialMatrices.trace_one : τ 1 = 1 := by
  have hn : (Fintype.card (A 0) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa only [map_one, Matrix.trace_one, inv_mul_cancel₀ hn] using M.trace_embedding 0 1

/-- The stage of a nested embedded matrix algebra. -/
def embeddedMatrixStage (s : ℕ) :
    MatrixHilbertStage (E := E) (F := centeredSubspace (V 1)) (α := A s) :=
  tracialMatrixStage τ V L (M.embedding s) hinner hleft (M.trace_embedding s)

omit [∀ s, Nonempty (A s)] in
@[simp] theorem embeddedMatrixStage_full (s : ℕ) (a : Matrix (A s) (A s) ℂ) :
    (embeddedMatrixStage τ V L hinner hleft M s).full a = V (M.embedding s a) := rfl

omit [∀ s, Nonempty (A s)] in
@[simp] theorem embeddedMatrixStage_center (s : ℕ) (a : Matrix (A s) (A s) ℂ) :
    (embeddedMatrixStage τ V L hinner hleft M s).center a =
      tracialCenter V (M.embedding s a) := rfl

omit [∀ s, Nonempty (A s)] in
theorem embeddedMatrixStage_full_mono :
    Monotone (fullMatrixStage (embeddedMatrixStage τ V L hinner hleft M)) := by
  intro s t h x hx
  obtain ⟨a, rfl⟩ := hx
  refine ⟨M.inclusion s t h a, ?_⟩
  simp only [embeddedMatrixStage_full, M.compatible]

omit [CompleteSpace E] in
/-- Trace preservation forces every compatible matrix inclusion to preserve
trace-zero matrices, regardless of the change in matrix size. -/
theorem NestedTracialMatrices.trace_zero_inclusion (s t : ℕ) (h : s ≤ t)
    (a : Matrix (A s) (A s) ℂ) (ha : Matrix.trace a = 0) :
    Matrix.trace (M.inclusion s t h a) = 0 := by
  have he : (Fintype.card (A t) : ℂ)⁻¹ * Matrix.trace (M.inclusion s t h a) = 0 := by
    rw [← M.trace_embedding, M.compatible, M.trace_embedding, ha, mul_zero]
  have hn : (Fintype.card (A t) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero hn)

theorem embeddedMatrixStage_center_mono :
    Monotone (centeredMatrixStage (embeddedMatrixStage τ V L hinner hleft M)) := by
  intro s t h x hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨M.inclusion s t h a,
    NestedTracialMatrices.trace_zero_inclusion τ V M s t h a ha, ?_⟩
  simp only [embeddedMatrixStage_center, M.compatible]

/-- Any centered matrix vector is represented by a trace-zero matrix in the
same stage. -/
theorem embeddedMatrixStage_center_trace_zero (s : ℕ) (a : Matrix (A s) (A s) ℂ) :
    ∃ b : Matrix (A s) (A s) ℂ, Matrix.trace b = 0 ∧
      (embeddedMatrixStage τ V L hinner hleft M s).center b =
        (embeddedMatrixStage τ V L hinner hleft M s).center a := by
  let c : ℂ := (Fintype.card (A s) : ℂ)⁻¹ * Matrix.trace a
  refine ⟨a - c • 1, ?_, ?_⟩
  · have hn : (Fintype.card (A s) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, c]
    field_simp
    ring
  · change tracialCenter V (M.embedding s (a - c • 1)) = tracialCenter V (M.embedding s a)
    rw [map_sub (M.embedding s), map_smul (M.embedding s), map_one (M.embedding s),
      map_sub, map_smul, tracialCenter_one,
      smul_zero, sub_zero]

/-- Centered-stage density follows from full-stage density and the actual
orthogonal projection; it is not an extra tower hypothesis. -/
theorem embeddedMatrixStage_center_dense :
    Dense (⋃ s, centeredMatrixStage (embeddedMatrixStage τ V L hinner hleft M) s) := by
  let P := (centeredSubspace (V 1)).orthogonalProjectionOnto
  have hP : Function.Surjective P := by
    intro x
    exact ⟨x, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  apply hP.denseRange.dense_of_mapsTo P.continuous M.dense
  intro x hx
  obtain ⟨s, a, rfl⟩ := Set.mem_iUnion.mp hx
  obtain ⟨b, hb, heq⟩ := embeddedMatrixStage_center_trace_zero τ V L hinner hleft M s a
  apply Set.mem_iUnion.mpr
  exact ⟨s, b, hb, heq⟩

variable [StarModule ℂ R]
  (htrace : ∀ a b, τ (a * b) = τ (b * a))
  (hdense : DenseRange V) (S : RealTracialSequence τ)

/-- Real algebra vectors give the actual fixed orthonormal sequence in the
centered tracial Hilbert space. -/
def realTracialHilbertSequence (n : ℕ) : centeredSubspace (V 1) :=
  tracialCenter V (S.vector n)

include hinner in
omit [CompleteSpace E] [StarModule ℂ R] in
@[simp] theorem coe_realTracialHilbertSequence (n : ℕ) :
    (realTracialHilbertSequence τ V S n : E) = V (S.vector n) :=
  coe_tracialCenter_of_trace_zero τ V hinner _ (S.trace_zero n)

include hinner in
omit [CompleteSpace E] [StarModule ℂ R] in
theorem realTracialHilbertSequence_orthonormal :
    Orthonormal ℂ (realTracialHilbertSequence τ V S) := by
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℂ (realTracialHilbertSequence τ V S i : E)
    (realTracialHilbertSequence τ V S j : E) = _
  rw [coe_realTracialHilbertSequence τ V hinner, coe_realTracialHilbertSequence τ V hinner,
    hinner, S.inner]

theorem realTracialHilbertSequence_fixed (n : ℕ) :
    centeredTracialConjugation τ V hinner htrace hdense
      (realTracialHilbertSequence τ V S n) = realTracialHilbertSequence τ V S n := by
  apply Subtype.ext
  change tracialConjugation τ V hinner htrace hdense
    (realTracialHilbertSequence τ V S n : E) = (realTracialHilbertSequence τ V S n : E)
  rw [coe_realTracialHilbertSequence τ V hinner, tracialConjugation_apply_vector,
    S.selfadjoint]

/-- Every scalar geometric field of the invariant-theory tower is now derived
from the actual tracial representation and raw matrix embeddings. The only
remaining sequence data is an algebraic real orthonormal sequence. -/
def tracialMatrixTowerOfEmbeddings
    (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop) :
    TracialMatrixTower (E := E) (F := centeredSubspace (V 1)) (A := A) where
  stage := embeddedMatrixStage τ V L hinner hleft M
  traceVector := V 1
  norm_traceVector := norm_tracialTraceVector τ V hinner
    (NestedTracialMatrices.trace_one τ V M)
  unit_realization s := by simp [embeddedMatrixStage]
  conjugation := centeredTracialConjugation τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M)
  conjugation_involutive := centeredTracialConjugation_involutive τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M)
  pairing := centeredTracialPairing τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M)
  pairing_conjugation := centeredTracialPairing_conjugation τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M)
  pairing_matrix s := centeredTracialPairing_matrix τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M) L
    (M.embedding s) hleft (M.trace_embedding s)
  inclusion s := M.inclusion 0 s (Nat.zero_le s)
  full_compatible s a := by simp only [embeddedMatrixStage_full, M.compatible]
  center_compatible s a := by simp only [embeddedMatrixStage_center, M.compatible]
  transition := M.inclusion
  full_transition s t h a := by simp only [embeddedMatrixStage_full, M.compatible]
  center_transition s t h a := by simp only [embeddedMatrixStage_center, M.compatible]
  full_mono := embeddedMatrixStage_full_mono τ V L hinner hleft M
  center_mono := embeddedMatrixStage_center_mono τ V L hinner hleft M
  full_dense := M.dense
  center_dense := embeddedMatrixStage_center_dense τ V L hinner hleft M
  size_tendsto := hsize
  realOrthonormal := realTracialHilbertSequence τ V S
  realOrthonormal_orthonormal := realTracialHilbertSequence_orthonormal τ V hinner S
  realOrthonormal_fixed := realTracialHilbertSequence_fixed τ V hinner htrace
    (NestedTracialMatrices.denseRange_vector τ V M) S

end KadisonSimilarity

end

end OAI
