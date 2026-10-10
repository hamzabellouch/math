import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteGNSNormality

namespace OAI

/-! Norm approximation transfers from concrete trace vectors to native
GNS vectors. The generic form keeps the concrete matrix construction small. -/

noncomputable section
namespace KadisonSimilarity

open Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : A →ₚ[ℂ] ℂ) (M : VonNeumannAlgebra H) (υ : TracialRepresentation M)
  (e : A ≃⋆ₐ[ℂ] M.toStarSubalgebra) (hτ : ∀ a, τ a = υ.trace (e a))

include hτ in
theorem gns_dist_eq_concrete_trace (a b : A) :
    dist (gnsTracialVector τ a) (gnsTracialVector τ b) =
      dist (baseVector υ (e a)) (baseVector υ (e b)) := by
  rw [← (concreteGNSIsometry τ M υ e hτ).isometry.dist_eq,
    concreteGNSIsometry_vector, concreteGNSIsometry_vector]

omit [CompleteSpace H] in
theorem gns_dist_eq_of_trace_vectors (V : A →ₗ[ℂ] H)
    (hV : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b)) (a b : A) :
    dist (gnsTracialVector τ a) (gnsTracialVector τ b) = dist (V a) (V b) := by
  apply (sq_eq_sq₀ (dist_nonneg : 0 ≤ dist _ _) dist_nonneg).mp
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub,
    norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    gnsTracialVector_inner, hV]

variable {I : Type*} {B : I → Type*} (φ : ∀ i, B i → A)

theorem gns_vectors_dense_of_approximation
    (h : ∀ a : A, ∀ ε : ℝ, 0 < ε → ∃ i b,
      dist (gnsTracialVector τ (φ i b)) (gnsTracialVector τ a) < ε) :
    Dense (⋃ i, Set.range (fun b => gnsTracialVector τ (φ i b))) := by
  intro ξ
  refine (gnsTracialVector_dense τ).induction_on ξ isClosed_closure ?_
  intro a
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨i, b, hb⟩ := h a ε hε
  exact ⟨gnsTracialVector τ (φ i b), Set.mem_iUnion.mpr ⟨i, b, rfl⟩,
    by simpa only [dist_comm] using hb⟩

end KadisonSimilarity

end

end OAI
