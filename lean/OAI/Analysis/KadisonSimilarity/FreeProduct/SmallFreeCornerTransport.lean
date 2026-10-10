import OAI.Analysis.KadisonSimilarity.FreeProduct.SmallFreeCornerData

namespace OAI

/-! The entire small-corner construction is transported together through
the chosen free-position embedding, so the Haar unitary and reflection
retain the same support projection as the matrix frame. -/

noncomputable section
namespace KadisonSimilarity

variable {A B α : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [Fintype α] [DecidableEq α]
  (φ : A →⋆ₐ[ℂ] B)

def MatrixUnitColumnFamily.map (F : MatrixUnitColumnFamily A α) :
    MatrixUnitColumnFamily B α where
  corner := φ F.corner
  corner_projection := F.corner_projection.map φ
  column i := φ (F.column i)
  initial i j := by
    rw [← map_star, ← map_mul, F.initial]
    split_ifs <;> simp only [map_zero]
  resolution := by
    simpa only [map_sum, map_mul, map_star, map_one] using congrArg φ F.resolution
  base := F.base
  base_column := congrArg φ F.base_column

variable (τA : A →ₗ[ℂ] ℂ) (τB : B →ₗ[ℂ] ℂ)
  (hφ : ∀ a, τB (φ a) = τA a)

def TracialMatrixUnitColumnFamily.map (F : TracialMatrixUnitColumnFamily τA α) :
    TracialMatrixUnitColumnFamily τB α where
  toMatrixUnitColumnFamily := F.toMatrixUnitColumnFamily.map φ
  trace_corner := (hφ _).trans F.trace_corner

variable {s : ℝ}

/-- A single embedding carries every piece of the small-corner data, with
the original numerical cutoff unchanged. -/
def SmallFreeCornerData.transport (Q : SmallFreeCornerData τA s) :
    SmallFreeCornerData τB s where
  size := Q.size
  size_pos := Q.size_pos
  frame := Q.frame.map φ τA τB hφ
  trace := Q.trace
  trace_pos := Q.trace_pos
  trace_lt := Q.trace_lt
  corner_trace := (hφ _).trans Q.corner_trace
  half := Q.half.transport φ hφ
  haar := transportedCornerUnitary φ Q.haar
  moments := Q.moments.transport φ τA τB hφ Q.haar

end KadisonSimilarity

end

end OAI
