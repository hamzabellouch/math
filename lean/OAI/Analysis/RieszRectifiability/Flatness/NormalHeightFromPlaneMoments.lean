import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LeastSquaredExcess
import OAI.Analysis.RieszRectifiability.Kernel.BallLocalization
import OAI.Analysis.RieszRectifiability.Kernel.NormalCoordinateTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem normalCoordinate_abs_le_plane_distance {q d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hdist : ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖)
    (i : Fin q) (x : Ambient d) :
    |normalCoordinate a N i x| ≤ infDist x (S : Set (Ambient d)) := by
  rw [hdist x]
  exact PiLp.norm_apply_le (N.toContinuousLinearMap.adjoint (x - a)) i

theorem normalCoordinate_memLp_on_ball {q d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q)
    (R : ℝ) (hR : 0 < R) : MemLp (normalCoordinate a N i) 2 (μ.restrict (ball 0 R)) :=
  lipschitz_height_memLp_on_ball m C μ hg (normalCoordinate a N i) 1
    (normalCoordinate_lipschitz a N i) 0 R hR

theorem normalized_normalCoordinate_memLp_on_ball {q d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q)
    (R : ℝ) (hR : 0 < R) (δ : ℝ) :
    MemLp (fun x => normalCoordinate a N i x / δ) 2 (μ.restrict (ball 0 R)) := by
  simpa only [div_eq_mul_inv] using! (normalCoordinate_memLp_on_ball m μ C hg a N i R hR).mul_const δ⁻¹

theorem normalCoordinate_second_moment_le_plane {q d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth m C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hdist : ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖)
    (i : Fin q) (R : ℝ) (hR : 0 < R) :
    (∫ x in ball (0 : Ambient d) R, normalCoordinate a N i x ^ 2 ∂μ) ≤
      ∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ := by
  apply integral_mono (normalCoordinate_memLp_on_ball m μ C hg a N i R hR).integrable_sq
    (squared_infDist_integrableOn_ball μ 0 R S hS)
  intro x
  have h := (sq_le_sq₀ (abs_nonneg (normalCoordinate a N i x)) infDist_nonneg).mpr
    (normalCoordinate_abs_le_plane_distance S a N hdist i x)
  simpa only [sq_abs] using! h

theorem normalCoordinate_dyadic_source_bound {n q d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hdist : ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖)
    (M δ b : ℝ) (l : ℕ)
    (hbound : (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      M * (δ * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) (i : Fin q) :
    (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate a N i x ^ 2 ∂μ) ≤
      δ ^ 2 * M * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2 := by
  calc
    _ ≤ ∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S : Set (Ambient d)) ^ 2 ∂μ :=
      normalCoordinate_second_moment_le_plane n μ C hg S hS a N hdist i ((2 : ℝ) ^ l) (by positivity)
    _ ≤ M * (δ * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2) := hbound
    _ = _ := by rw [pow_add ((2 : ℝ) ^ l) n 2]; ring

end

end RieszRectifiability

end OAI
