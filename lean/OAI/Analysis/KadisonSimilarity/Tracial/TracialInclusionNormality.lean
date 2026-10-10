import OAI.Analysis.KadisonSimilarity.Tracial.GNSVectorDensity
import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyDischarge
import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorTrace

namespace OAI

/-! A trace-preserving inclusion with closed source trace-vector balls has
normal range in a faithful concrete finite trace representation. -/

noncomputable section
namespace KadisonSimilarity

open Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u v
variable {A : Type u} {H : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (υ : TracialRepresentation M)
  (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] M.toStarSubalgebra)
  (hφ : ∀ a, υ.trace (φ a) = τ a)

include hφ

omit [StarOrderedRing A] in
private theorem tracePreservingVector_inner (a b : A) :
    inner ℂ (baseVector υ (φ a)) (baseVector υ (φ b)) = τ (star a * b) := by
  rw [baseVector_inner_trace, ← map_star φ, ← map_mul φ, hφ]

private theorem tracePreservingVector_norm (a : A) :
    ‖baseVector υ (φ a)‖ = ‖gnsTracialVector τ a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    tracePreservingVector_inner υ τ φ hφ, gnsTracialVector_inner]

def tracialInclusionIsometry : τ.GNS →ₗᵢ[ℂ] H :=
  ((baseVector υ).comp φ.toLinearMap).extendOfIsometry
    (gnsTracialVector_dense τ) (tracePreservingVector_norm υ τ φ hφ)

@[simp] theorem tracialInclusionIsometry_vector (a : A) :
    tracialInclusionIsometry υ τ φ hφ (gnsTracialVector τ a) = baseVector υ (φ a) :=
  LinearMap.extendOfIsometry_eq _ (gnsTracialVector_dense τ)
    (tracePreservingVector_norm υ τ φ hφ) a

theorem tracialInclusion_trace_balls_closed
    (hclosed : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (C : ℝ) :
    IsClosed ((fun a => baseVector υ (φ a)) '' Metric.closedBall (0 : A) C) := by
  let J := tracialInclusionIsometry υ τ φ hφ
  have heq : (fun a => baseVector υ (φ a)) '' Metric.closedBall (0 : A) C =
      J '' (gnsTracialVector τ '' Metric.closedBall (0 : A) C) := by
    rw [Set.image_image]
    congr 1
    funext a
    exact (tracialInclusionIsometry_vector υ τ φ hφ a).symm
  rw [heq]
  exact J.isometry.isClosedEmbedding.isClosedMap _ (hclosed C)

theorem tracialInclusion_normal_range
    (hclosed : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C)) :
    (M.toStarSubalgebra.subtype.comp φ).range =
      (representationVonNeumannAlgebra (M.toStarSubalgebra.subtype.comp φ)).toStarSubalgebra := by
  let σ := M.toStarSubalgebra.subtype.comp φ
  apply le_antisymm
  · rintro T ⟨a, rfl⟩
    exact mem_representationVonNeumannAlgebra σ a
  · intro T hT
    have hTM : T ∈ M := by
      change T ∈ representationVonNeumannAlgebra σ at hT
      rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
      rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
      intro b hb
      apply hT b
      rintro _ ⟨a, rfl⟩
      exact hb _ (φ a).property
    let x : M.toStarSubalgebra := ⟨T, hTM⟩
    have hx : baseVector υ x ∈ closure
        ((fun a => baseVector υ (φ a)) '' Metric.closedBall (0 : A) (‖T‖ + 1)) := by
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      let δ := min 1 (ε / 2)
      have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
      have hδ1 : δ ≤ 1 := min_le_left _ _
      have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
      obtain ⟨a, han, ha, _⟩ := twoVectorKaplanskyInput σ T hT υ.vector υ.vector δ hδ
      refine ⟨baseVector υ (φ a), ⟨a, ?_, rfl⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using
          han.trans (show ‖T‖ + δ ≤ ‖T‖ + 1 by linarith)
      · rw [dist_eq_norm, norm_sub_rev]
        exact ha.trans_lt hδε
    obtain ⟨a, _, ha⟩ := (tracialInclusion_trace_balls_closed υ τ φ hφ hclosed (‖T‖ + 1)).closure_subset hx
    have hax : φ a = x := by
      apply sub_eq_zero.mp
      apply υ.separating
      change baseVector υ (φ a - x) = 0
      change baseVector υ (φ a) = baseVector υ x at ha
      rw [map_sub, ha, sub_self]
    exact ⟨a, congrArg Subtype.val hax⟩

theorem tracialInclusion_normal_range_of_predual
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (hτ : BoundedHochschild.TraceInPredual e τ) :
    (M.toStarSubalgebra.subtype.comp φ).range =
      (representationVonNeumannAlgebra (M.toStarSubalgebra.subtype.comp φ)).toStarSubalgebra :=
  tracialInclusion_normal_range υ τ φ hφ (predual_gns_trace_balls_closed e τ hτ)

end KadisonSimilarity

end

end OAI
