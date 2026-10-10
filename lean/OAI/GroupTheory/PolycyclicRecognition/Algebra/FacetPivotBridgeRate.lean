import OAI.GroupTheory.PolycyclicRecognition.Geometry.FacetRootSwitch
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceVolumeComparison

namespace OAI

/-! # A vanishing rate for the actual bridge at the facet pivot -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

theorem distance_rate_tendsto_zero
    {X : Type*} [PseudoMetricSpace X] (scale : ℕ → ℝ) (hs : ∀ n, 0 < scale n)
    (a b : ℕ → X)
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, dist (a n) (b n) ≤ ε * scale n) :
    Tendsto (fun n => dist (a n) (b n) / scale n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hnear (ε / 2) (by positivity)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg dist_nonneg (hs n).le)]
  exact ((div_le_iff₀ (hs n)).mpr hn).trans_lt (half_lt_self hε)

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- No bridge estimate is postulated: root distortion at the exact facet
height supplies a nonnegative error rate tending to zero, uniformly over
the initial source state. -/
theorem exists_facet_pivot_bridge_rate
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (v : rootSpace H χ) (pivot : H) (scale R η t : ℕ → ℝ)
    (hs : Tendsto scale atTop atTop) (hscale : ∀ n, 0 < scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (hη : Tendsto η atTop (𝓝 0))
    (ht : ∀ n, |t n| ≤ R n * Real.exp ((χ pivot + η n) * scale n)) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ n x, dist (x * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (x * Exp (t n • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ δ n * scale n := by
  let B := ‖(finBasis ℝ H).equivFun pivot‖
  let RH := fun n => (B + 1) * (1 + scale n) ^ 1
  have hB : 0 ≤ B := norm_nonneg _
  have hRH0 : ∀ n, 0 ≤ RH n := fun n =>
    mul_nonneg (by linarith) (pow_nonneg (by linarith [hscale n]) _)
  have hRH : HasSubexponentialUpperBoundSeq scale RH :=
    (subexponential_upper_polynomial (by linarith : 0 < B + 1) 1).along_sequence hs
  let left := fun n => Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let right := fun n => Exp (t n • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * left n
  have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      dist (left n) (right n) ≤ ε * scale n := by
    intro ε hε
    filter_upwards [facet_root_switch_sublinear T H χ hχ Exp hExp realize v
      scale RH R η (χ pivot) hs (fun n => (hscale n).le) hRH0 hR0 hRH hR hη ε hε] with n hn
    have hsize : ‖(finBasis ℝ H).equivFun (scale n • pivot)‖ ≤ RH n := by
      rw [map_smul, norm_smul, Real.norm_of_nonneg (hscale n).le]
      change scale n * B ≤ (B + 1) * (1 + scale n) ^ 1
      nlinarith [hscale n]
    have hfacet : χ (scale n • pivot) = χ pivot * scale n := by
      rw [map_smul, smul_eq_mul, mul_comm]
    simpa only [left, right, one_mul, SetLike.val_smul] using
      hn 1 (scale n • pivot) (t n) hsize hfacet (ht n)
  let δ := fun n => dist (left n) (right n) / scale n
  refine ⟨δ, fun n => div_nonneg dist_nonneg (hscale n).le,
    distance_rate_tendsto_zero scale hscale left right hnear, ?_⟩
  intro n x
  have he : δ n * scale n = dist (left n) (right n) :=
    div_mul_cancel₀ _ (hscale n).ne'
  rw [he, mul_assoc, dist_mul_left]

end PolycyclicRecognition

end

end OAI
