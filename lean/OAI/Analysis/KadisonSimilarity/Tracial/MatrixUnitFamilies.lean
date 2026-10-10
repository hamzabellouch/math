import OAI.Analysis.KadisonSimilarity.Tracial.MatrixCornerFrames
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixTower
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace

namespace OAI

/-! Finite partial-isometry frames constructed from an actual unital matrix
star homomorphism. No frame-existence assumption is used. -/

noncomputable section
namespace KadisonSimilarity

variable {P α : Type*} [CStarAlgebra P] [Fintype α] [DecidableEq α]

/-- The image of an ordinary matrix unit in the ambient C-star algebra. -/
def embeddedMatrixUnit (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i j : α) : P :=
  ι (Matrix.single i j 1)

@[simp] theorem embeddedMatrixUnit_star (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i j : α) :
    star (embeddedMatrixUnit ι i j) = embeddedMatrixUnit ι j i := by
  unfold embeddedMatrixUnit
  rw [← map_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]

theorem embeddedMatrixUnit_mul (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i j k l : α) :
    embeddedMatrixUnit ι i j * embeddedMatrixUnit ι k l =
      if j = k then embeddedMatrixUnit ι i l else 0 := by
  unfold embeddedMatrixUnit
  rw [← map_mul]
  by_cases h : j = k
  · subst k
    simp
  · rw [Matrix.single_mul_single_of_ne (1 : ℂ) i j k h (1 : ℂ)]
    simp only [map_zero, h, ↓reduceIte]

/-- Diagonal matrix units are actual star projections. -/
theorem embeddedMatrixUnit_isStarProjection (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i : α) :
    IsStarProjection (embeddedMatrixUnit ι i i) := by
  refine ⟨?_, ?_⟩
  · change embeddedMatrixUnit ι i i * embeddedMatrixUnit ι i i = _
    simp [embeddedMatrixUnit_mul]
  · exact embeddedMatrixUnit_star ι i i

/-- The diagonal images resolve the unit because the embedding is unital. -/
theorem sum_embeddedMatrixUnit_diagonal (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) :
    ∑ i : α, embeddedMatrixUnit ι i i = 1 := by
  unfold embeddedMatrixUnit
  rw [← map_sum, Matrix.sum_single_one, map_one]

/-- The precise finite-frame data consumed by full-column coordinates. -/
structure MatrixUnitColumnFamily (P α : Type*) [CStarAlgebra P]
    [Fintype α] [DecidableEq α] where
  corner : P
  corner_projection : IsStarProjection corner
  column : α → P
  initial : ∀ i j, star (column i) * column j = if i = j then corner else 0
  resolution : ∑ i, column i * star (column i) = 1
  base : α
  base_column : column base = corner

/-- Taking a single column of embedded matrix units supplies the full frame. -/
def matrixUnitColumnFamilyOfEmbedding (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i₀ : α) :
    MatrixUnitColumnFamily P α where
  corner := embeddedMatrixUnit ι i₀ i₀
  corner_projection := embeddedMatrixUnit_isStarProjection ι i₀
  column i := embeddedMatrixUnit ι i i₀
  initial i j := by
    rw [embeddedMatrixUnit_star, embeddedMatrixUnit_mul]
  resolution := by
    simp only [embeddedMatrixUnit_star, embeddedMatrixUnit_mul, ↓reduceIte]
    exact sum_embeddedMatrixUnit_diagonal ι
  base := i₀
  base_column := rfl

@[simp] theorem matrixUnitColumnFamilyOfEmbedding_corner
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i₀ : α) :
    (matrixUnitColumnFamilyOfEmbedding ι i₀).corner = ι (Matrix.single i₀ i₀ 1) := rfl

@[simp] theorem matrixUnitColumnFamilyOfEmbedding_column
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] P) (i₀ i : α) :
    (matrixUnitColumnFamilyOfEmbedding ι i₀).column i = ι (Matrix.single i i₀ 1) := rfl

/-- Normalized trace preservation gives the reciprocal-dimension trace of
all the diagonal projections, and hence of the chosen initial corner. -/
theorem trace_embeddedMatrixUnit_diagonal
    (τ : P →ₗ[ℂ] ℂ) (ι : Matrix α α ℂ →⋆ₐ[ℂ] P)
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) (i : α) :
    τ (embeddedMatrixUnit ι i i) = 1 / (Fintype.card α : ℂ) := by
  rw [embeddedMatrixUnit, htrace, Matrix.trace_single_eq_same, mul_one, one_div]

/-- The frame together with the corner trace used in small-corner estimates. -/
structure TracialMatrixUnitColumnFamily (τ : P →ₗ[ℂ] ℂ) (α : Type*)
    [Fintype α] [DecidableEq α] extends MatrixUnitColumnFamily P α where
  trace_corner : τ corner = 1 / (Fintype.card α : ℂ)

/-- A trace-preserving unital matrix embedding supplies both frame and trace. -/
def tracialMatrixUnitColumnFamilyOfEmbedding
    (τ : P →ₗ[ℂ] ℂ) (ι : Matrix α α ℂ →⋆ₐ[ℂ] P)
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) (i₀ : α) :
    TracialMatrixUnitColumnFamily τ α where
  toMatrixUnitColumnFamily := matrixUnitColumnFamilyOfEmbedding ι i₀
  trace_corner := trace_embeddedMatrixUnit_diagonal τ ι htrace i₀

/-- A nonempty finite matrix index type provides a distinguished corner
without an additional choice of frame data. -/
def tracialMatrixUnitColumnFamilyOfNonempty [Nonempty α]
    (τ : P →ₗ[ℂ] ℂ) (ι : Matrix α α ℂ →⋆ₐ[ℂ] P)
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) :
    TracialMatrixUnitColumnFamily τ α :=
  tracialMatrixUnitColumnFamilyOfEmbedding τ ι htrace (Classical.choice ‹Nonempty α›)

namespace MatrixUnitColumnFamily

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Relabeling a finite frame preserves its initial projection and resolution. -/
def reindex (F : MatrixUnitColumnFamily P α) (e : β ≃ α) : MatrixUnitColumnFamily P β where
  corner := F.corner
  corner_projection := F.corner_projection
  column i := F.column (e i)
  initial i j := by simpa using F.initial (e i) (e j)
  resolution := (e.sum_comp (fun i => F.column i * star (F.column i))).trans F.resolution
  base := e.symm F.base
  base_column := by simpa only [e.apply_symm_apply] using F.base_column

@[simp] theorem reindex_corner (F : MatrixUnitColumnFamily P α) (e : β ≃ α) :
    (F.reindex e).corner = F.corner := rfl

@[simp] theorem reindex_column (F : MatrixUnitColumnFamily P α) (e : β ≃ α) (i : β) :
    (F.reindex e).column i = F.column (e i) := rfl

end MatrixUnitColumnFamily

namespace TracialMatrixUnitColumnFamily

variable {τ : P →ₗ[ℂ] ℂ} {β : Type*} [Fintype β] [DecidableEq β]

/-- The normalized corner trace is preserved when a finite frame is relabeled. -/
def reindex (F : TracialMatrixUnitColumnFamily τ α) (e : β ≃ α) :
    TracialMatrixUnitColumnFamily τ β where
  toMatrixUnitColumnFamily := F.toMatrixUnitColumnFamily.reindex e
  trace_corner := by
    change τ F.corner = 1 / (Fintype.card β : ℂ)
    rw [Fintype.card_congr e]
    exact F.trace_corner

end TracialMatrixUnitColumnFamily

section NestedMatrices

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  {τ : P →ₗ[ℂ] ℂ} {V : P →ₗ[ℂ] E}

/-- Each actual tracial matrix stage supplies its finite corner frame. -/
def NestedTracialMatrices.columnFamily (M : NestedTracialMatrices (A := A) τ V)
    (s : ℕ) (i₀ : A s) : TracialMatrixUnitColumnFamily τ (A s) :=
  tracialMatrixUnitColumnFamilyOfEmbedding τ (M.embedding s) (M.trace_embedding s) i₀

/-- The same actual frame on `Fin(card(A s))`, as required by finite Hilbert
amplification and the full-column coordinate construction. -/
def NestedTracialMatrices.finColumnFamily (M : NestedTracialMatrices (A := A) τ V)
    (s : ℕ) (i₀ : A s) : TracialMatrixUnitColumnFamily τ (Fin (Fintype.card (A s))) :=
  (M.columnFamily s i₀).reindex (Fintype.equivFin (A s)).symm

@[simp] theorem NestedTracialMatrices.finColumnFamily_corner
    (M : NestedTracialMatrices (A := A) τ V) (s : ℕ) (i₀ : A s) :
    (M.finColumnFamily s i₀).corner = M.embedding s (Matrix.single i₀ i₀ 1) := rfl

@[simp] theorem NestedTracialMatrices.finColumnFamily_column
    (M : NestedTracialMatrices (A := A) τ V) (s : ℕ) (i₀ : A s)
    (i : Fin (Fintype.card (A s))) :
    (M.finColumnFamily s i₀).column i =
      M.embedding s (Matrix.single ((Fintype.equivFin (A s)).symm i) i₀ 1) := rfl

@[simp] theorem NestedTracialMatrices.finColumnFamily_base
    (M : NestedTracialMatrices (A := A) τ V) (s : ℕ) (i₀ : A s) :
    (M.finColumnFamily s i₀).base = Fintype.equivFin (A s) i₀ := rfl

/-- A nonempty stage gives the finite amplification frame without any
additional existence hypothesis. -/
def NestedTracialMatrices.nonemptyFinColumnFamily [∀ s, Nonempty (A s)]
    (M : NestedTracialMatrices (A := A) τ V) (s : ℕ) :
    TracialMatrixUnitColumnFamily τ (Fin (Fintype.card (A s))) :=
  M.finColumnFamily s (Classical.choice (inferInstance : Nonempty (A s)))

end NestedMatrices

end KadisonSimilarity

end

end OAI
