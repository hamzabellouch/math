import OAI.Analysis.KadisonSimilarity.Tracial.TracialBoundedBalls
import OAI.Analysis.KadisonSimilarity.Tracial.GNSTracialGeometry

namespace OAI

/-! A trace realized faithfully in a concrete finite von Neumann algebra
has normal native GNS range. The original trace vector need not be cyclic. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped CStarAlgebra ComplexOrder

/-- Normality of the native representation of the chosen positive trace. -/
def HasNormalGNS {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) : Prop :=
  τ.gnsStarAlgHom.range = (representationVonNeumannAlgebra τ.gnsStarAlgHom).toStarSubalgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : A →ₚ[ℂ] ℂ) (M : VonNeumannAlgebra H)

local instance concreteGNS_closed :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := base_norm_closed M

variable (υ : TracialRepresentation M) (e : A ≃⋆ₐ[ℂ] M.toStarSubalgebra)
  (hτ : ∀ a, τ a = υ.trace (e a))

include hτ in
private theorem concreteTraceVector_norm (a : A) :
    ‖baseVector υ (e a)‖ = ‖gnsTracialVector τ a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    baseVector_inner_trace, gnsTracialVector_inner, hτ, map_mul e (star a) a]
  have hs : e (star a) = star (e a) := e.toStarAlgHom.map_star' a
  rw [hs]

/-- The native GNS space embeds isometrically into the concrete trace space. -/
def concreteGNSIsometry : τ.GNS →ₗᵢ[ℂ] H :=
  ((baseVector υ).comp e.toAlgEquiv.toLinearMap).extendOfIsometry
    (gnsTracialVector_dense τ) (concreteTraceVector_norm τ M υ e hτ)

@[simp] theorem concreteGNSIsometry_vector (a : A) :
    concreteGNSIsometry τ M υ e hτ (gnsTracialVector τ a) = baseVector υ (e a) :=
  LinearMap.extendOfIsometry_eq _ (gnsTracialVector_dense τ)
    (concreteTraceVector_norm τ M υ e hτ) a

include υ e hτ in
/-- Weak-operator bounded limits yield closed native GNS trace-vector balls. -/
theorem concrete_gns_trace_balls_closed (C : ℝ) :
    IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C) := by
  let J := concreteGNSIsometry τ M υ e hτ
  have hn (a : A) : ‖e a‖ = ‖a‖ :=
    (NonUnitalStarAlgHom.isometry e.toStarAlgHom e.injective).norm_map_of_map_zero
      (map_zero e.toStarAlgHom) a
  have heq : gnsTracialVector τ '' Metric.closedBall (0 : A) C =
      J ⁻¹' {ξ : H | ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧
        (b : H →L[ℂ] H) υ.vector = ξ} := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨e a, ?_, (concreteGNSIsometry_vector τ M υ e hτ a).symm⟩
      rw [hn]
      simpa only [Metric.mem_closedBall, dist_zero_right] using ha
    · rintro ⟨b, hb, hξ⟩
      obtain ⟨a, rfl⟩ := e.surjective b
      refine ⟨a, ?_, J.injective ?_⟩
      · change ‖e a‖ ≤ C at hb
        rw [hn] at hb
        simpa only [Metric.mem_closedBall, dist_zero_right] using hb
      · exact (concreteGNSIsometry_vector τ M υ e hτ a).trans hξ
  rw [heq]
  exact (trace_ball_isClosed υ C).preimage J.continuous

include υ e hτ in
/-- A concrete normal trace gives normality of its native left action. -/
theorem concrete_gns_normal_range :
    τ.gnsStarAlgHom.range = (representationVonNeumannAlgebra τ.gnsStarAlgHom).toStarSubalgebra := by
  have htr : ∀ a b, τ (a * b) = τ (b * a) := by
    intro a b
    rw [hτ, hτ, map_mul e a b, map_mul e b a, υ.trace_mul_comm]
  exact (gnsTracialGeometry τ htr).normal_range_of_closed_trace_balls
    (concrete_gns_trace_balls_closed τ M υ e hτ)

end KadisonSimilarity

end

end OAI
