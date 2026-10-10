import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BoundedBoxContainment
import OAI.Analysis.RieszRectifiability.Limits.FiniteAffineVectorLimit
import OAI.Analysis.RieszRectifiability.Packing.NormalFrameExcessLimit
import OAI.Analysis.RieszRectifiability.Kernel.NormalCoordinateMoments

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology WithLp
open scoped NNReal ENNReal

theorem normal_frame_excess_of_common_affine_coordinates {n q d : ℕ}
    (e : (Fin n → ℝ) → Ambient d) (π : Ambient d → Fin n → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (z : Ambient d) (Llim : Ambient n →ₗᵢ[ℝ] Ambient d)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (a : ℕ → Ambient d) (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d)
    (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
    (horth : ∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0)
    (hsplit : ∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
      N j ((N j).toContinuousLinearMap.adjoint y) = y)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (hw : ∀ i H j, MemLp (fun x => normalCoordinate (a j) (N j) i x / δ j) 2
      ((μ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B₀ : ℕ → ℝ)
    (hB₀ : ∀ i H j, (∫ x, (normalCoordinate (a j) (N j) i x / δ j) ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
    (c : Fin q → ℝ) (M : Fin q → Ambient n →L[ℝ] ℝ)
    (hscalar : ∀ i H, Tendsto (fun j => ∫ x,
      (normalCoordinate (a j) (N j) i x / δ j - ambientAffineHeight z Llim (c i) (M i) x) ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop (𝓝 0)) :
    ∀ r : ℝ, 0 ≤ r →
      Tendsto (fun j => squaredExcess n (μ j) (e 0) r / δ j ^ 2) atTop (𝓝 0) := by
  obtain ⟨v₀, B, hstrong⟩ := exists_vector_affine_strong_limit_of_coordinates z (e 0) Llim
    π K Q hπ μ (fun i j x => normalCoordinate (a j) (N j) i x / δ j) hw c M hscalar
  simp only [normalCoordinate_normalized_vector] at hstrong
  intro r hr
  obtain ⟨H, hH⟩ := exists_boundedProjectionRegion_containing_ball e π K Q hπ hleft r
  have hraw := fun j => normalizedNormalHeight_second_moment_bound
    ((μ j).restrict (boundedProjectionRegion π (e 0) K H)) (a j) (N j) (δ j)
    (fun i => hw i H j) (B₀ H) (fun i => hB₀ i H j)
  have hrawBall : ∀ j, Integrable (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2)
      ((μ j).restrict (ball (e 0) r)) :=
    fun j => IntegrableOn.mono_set (hraw j).1 hH
  have hbound : ∀ j, (∫ x in ball (e 0) r,
      ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2 ∂μ j) ≤ (q : ℝ) * B₀ H := by
    intro j
    exact (setIntegral_mono_set (hraw j).1
      (Eventually.of_forall fun x => sq_nonneg ‖normalizedNormalHeight (a j) (N j) (δ j) x‖)
      (Eventually.of_forall fun x hx => hH hx)).trans (hraw j).2
  have herr : ∀ j, Integrable
      (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x - (v₀ + B x)‖ ^ 2)
      ((μ j).restrict (ball (e 0) r)) :=
    fun j => IntegrableOn.mono_set ((hstrong H).1 j) hH
  have hball : Tendsto (fun j => ∫ x in ball (e 0) r,
      ‖normalizedNormalHeight (a j) (N j) (δ j) x - (v₀ + B x)‖ ^ 2 ∂μ j) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun j => integral_nonneg fun x => sq_nonneg ‖normalizedNormalHeight (a j) (N j) (δ j) x - (v₀ + B x)‖)
      _ (hstrong H).2
    intro j
    exact setIntegral_mono_set ((hstrong H).1 j)
      (Eventually.of_forall fun x => sq_nonneg ‖normalizedNormalHeight (a j) (N j) (δ j) x - (v₀ + B x)‖)
      (Eventually.of_forall fun x hx => hH hx)
  exact moving_normal_frame_squaredExcess_ratio_tendsto_zero μ (e 0) r hr a L N horth hsplit
    δ hδ hδlim v₀ B hrawBall ((q : ℝ) * B₀ H) hbound herr hball

end

end RieszRectifiability

end OAI
