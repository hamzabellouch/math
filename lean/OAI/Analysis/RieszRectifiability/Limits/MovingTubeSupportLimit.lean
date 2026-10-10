import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitSupport
import OAI.Analysis.RieszRectifiability.Packing.FittingPlaneFrameSubsequence

namespace OAI

/-!
# Support containment from moving tubes

Nonnegative, uniformly Lipschitz functions that vanish along the approximating
supports also vanish on the support of a compact-test limit measure. Applied to
distances from affine planes with convergent frames, this identifies the plane
containing the limiting support.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology EuclideanGeometry
open scoped NNReal ENNReal

theorem moving_lipschitz_tubes_vanish_on_limit_support {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (f : ℕ → Ambient d → ℝ)
    (hf : ∀ j, LipschitzWith 1 (f j)) (hnn : ∀ j x, 0 ≤ f j x)
    (htube : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∀ᶠ j in atTop, ∀ x ∈ ball (0 : Ambient d) R, x ∈ (μ j).support → f j x < ε) :
    ∀ x ∈ ν.support, Tendsto (fun j => f j x) atTop (𝓝 0) := by
  intro x hx
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact Eventually.of_forall (fun j => hr.trans_le (hnn j x))
  · intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hR : 0 < ‖x‖ + ε / 2 := by linarith [norm_nonneg x]
    filter_upwards [compactTestConvergence_nearby_support μ ν hlocal x hx (ε / 2) hhalf,
      htube (‖x‖ + ε / 2) (ε / 2) hR hhalf] with j hnear hjtube
    obtain ⟨y, hysupp, hyball⟩ := hnear
    have hyx : dist y x < ε / 2 := hyball
    have hy0 : y ∈ ball (0 : Ambient d) (‖x‖ + ε / 2) := by
      have htri := dist_triangle y x (0 : Ambient d)
      simp only [mem_ball, dist_zero_right] at htri ⊢
      linarith
    have hsmall := hjtube y hy0 hysupp
    have hdiff : f j x - f j y ≤ dist x y := by
      have h := (hf j).dist_le_mul x y
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
      exact (le_abs_self _).trans h
    rw [dist_comm x y] at hdiff
    linarith

theorem moving_plane_limit_support {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, (S j : Set (Ambient d)).Nonempty)
    (a : ℕ → Ambient d) (ha : ∀ j, a j ∈ S j) (ha0 : Tendsto a atTop (𝓝 0))
    (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d) (hL : ∀ j, (L j).toLinearMap.range = (S j).direction)
    (Llim : Ambient n →ₗᵢ[ℝ] Ambient d)
    (hLlim : Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap))
    (hmoment : ∀ R : ℝ, 0 < R →
      Tendsto (fun j => ∫ x in ball (0 : Ambient d) R,
        infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0)) :
    ν.support ⊆ (Llim.toLinearMap.range : Set (Ambient d)) := by
  have htube : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∀ᶠ j in atTop, ∀ x ∈ ball (0 : Ambient d) R, x ∈ (μ j).support →
        infDist x (S j : Set (Ambient d)) < ε := by
    intro R ε hR hε
    exact moving_plane_support_tube_of_moments n μ C hC hlower hdiam S hS 0 R
      (hmoment (R + 1) (by linarith)) ε hε
  have hzero := moving_lipschitz_tubes_vanish_on_limit_support μ ν hlocal
    (fun j x => infDist x (S j : Set (Ambient d)))
    (fun j => lipschitz_infDist_pt _) (fun _ _ => infDist_nonneg) htube
  intro x hx
  have heq : ∀ j, infDist x (S j : Set (Ambient d)) = dist x (tangentPlaneProjection (a j) (L j) x) := by
    intro j
    let : Nonempty (S j) := (hS j).to_subtype
    rw [← dist_orthogonalProjection_eq_infDist (S j) x,
      affine_plane_projection_of_frame (S j) (a j) (ha j) (L j) (hL j)]
  have hdist0 : Tendsto (fun j => dist x (tangentPlaneProjection (a j) (L j) x)) atTop (𝓝 0) := by
    simpa only [heq] using! hzero x hx
  have hdistlim : Tendsto (fun j => dist x (tangentPlaneProjection (a j) (L j) x)) atTop
      (𝓝 (dist x (tangentPlaneProjection 0 Llim x))) :=
    tendsto_const_nhds.dist (tangentPlaneProjection_tendsto a 0 ha0 L Llim hLlim x)
  have he := dist_eq_zero.mp (tendsto_nhds_unique hdistlim hdist0)
  simp only [tangentPlaneProjection, zero_add, sub_zero] at he
  exact ⟨Llim.toContinuousLinearMap.adjoint x, he.symm⟩

end

end RieszRectifiability

end OAI
