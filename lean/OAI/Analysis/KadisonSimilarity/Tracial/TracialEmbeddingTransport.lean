import OAI.Analysis.KadisonSimilarity.Tracial.GNSTracialGeometry
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixTower
import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseGeometry

namespace OAI

/-! A trace-preserving embedding transports the completed tracial space,
the dense matrix tower, and its real orthonormal sequence to its actual
range. No normal-form or matrix-density assumption is added at the target. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {R P H : Type*} [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder R] [StarOrderedRing R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : R →ₚ[ℂ] ℂ) (G : TracialCornerGeometry P H)
  (φ : R →⋆ₐ[ℂ] P) (hφ : ∀ a, G.trace (φ a) = τ a)

include hφ in
theorem tracialRangeVector_norm (a : R) :
    ‖G.baseVector φ.range (φ.rangeRestrict a)‖ = ‖gnsTracialVector τ a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    G.baseVector_inner, gnsTracialVector_inner]
  change (G.trace (star (φ a) * φ a)).re = (τ (star a * a)).re
  rw [← map_star, ← map_mul, hφ]

/-- The completed trace-preserving map lands in the actual closed range space. -/
def tracialRangeIsometry : τ.GNS →ₗᵢ[ℂ] G.baseSpace φ.range :=
  ((G.baseVector φ.range).comp φ.rangeRestrict.toLinearMap).extendOfIsometry
    (gnsTracialVector_dense τ) (tracialRangeVector_norm τ G φ hφ)

@[simp] theorem tracialRangeIsometry_vector (a : R) :
    tracialRangeIsometry τ G φ hφ (gnsTracialVector τ a) =
      G.baseVector φ.range (φ.rangeRestrict a) :=
  LinearMap.extendOfIsometry_eq _ (gnsTracialVector_dense τ)
    (tracialRangeVector_norm τ G φ hφ) a

theorem tracialRangeIsometry_surjective :
    Function.Surjective (tracialRangeIsometry τ G φ hφ) := by
  intro x
  have hc : IsClosed (Set.range (tracialRangeIsometry τ G φ hφ)) :=
    (tracialRangeIsometry τ G φ hφ).isometry.isClosedEmbedding.isClosed_range
  change x ∈ Set.range (tracialRangeIsometry τ G φ hφ)
  refine (G.baseVector_dense φ.range).induction_on x hc ?_
  rintro ⟨a, b, rfl⟩
  exact ⟨gnsTracialVector τ b, tracialRangeIsometry_vector τ G φ hφ b⟩

/-- The range completion is unitarily the original tracial GNS space. -/
def tracialRangeUnitary : τ.GNS ≃ₗᵢ[ℂ] G.baseSpace φ.range :=
  LinearIsometryEquiv.ofSurjective (tracialRangeIsometry τ G φ hφ)
    (tracialRangeIsometry_surjective τ G φ hφ)

@[simp] theorem tracialRangeUnitary_vector (a : R) :
    tracialRangeUnitary τ G φ hφ (gnsTracialVector τ a) =
      G.baseVector φ.range (φ.rangeRestrict a) :=
  tracialRangeIsometry_vector τ G φ hφ a

variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
  [∀ n, Nonempty (I n)]

/-- A concrete matrix tower stays dense after a trace-preserving embedding. -/
def transportTracialMatrices
    (M : NestedTracialMatrices (A := I) τ.toLinearMap (gnsTracialVector τ)) :
    NestedTracialMatrices (A := I)
      (G.trace.comp φ.range.subtype.toLinearMap) (G.baseVector φ.range) where
  embedding n := φ.rangeRestrict.comp (M.embedding n)
  trace_embedding n a := by
    change G.trace (φ (M.embedding n a)) = _
    rw [hφ]
    exact M.trace_embedding n a
  inclusion := M.inclusion
  compatible n m h a := by
    change φ.rangeRestrict (M.embedding m (M.inclusion n m h a)) = _
    rw [M.compatible]
    rfl
  dense := by
    have hd := (tracialRangeIsometry_surjective τ G φ hφ).denseRange.dense_image
      (tracialRangeIsometry τ G φ hφ).continuous M.dense
    apply hd.mono
    rintro _ ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp hx with ⟨n, a, rfl⟩
    exact Set.mem_iUnion.mpr
      ⟨n, a, (tracialRangeIsometry_vector τ G φ hφ (M.embedding n a)).symm⟩

/-- The real trace-orthonormal sequence is transported algebraically. -/
def transportRealTracialSequence (S : RealTracialSequence τ.toLinearMap) :
    RealTracialSequence (G.trace.comp φ.range.subtype.toLinearMap) where
  vector n := φ.rangeRestrict (S.vector n)
  trace_zero n := by change G.trace (φ (S.vector n)) = 0; rw [hφ]; exact S.trace_zero n
  selfadjoint n := by rw [← map_star, S.selfadjoint]
  inner n m := by
    change G.trace (star (φ (S.vector n)) * φ (S.vector m)) = _
    rw [← map_star, ← map_mul, hφ]
    exact S.inner n m

end KadisonSimilarity

end

end OAI
