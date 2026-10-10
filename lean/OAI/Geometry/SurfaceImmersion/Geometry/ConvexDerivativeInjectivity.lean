import OAI.Geometry.SurfaceImmersion.Geometry.CompactTranslationImmersion
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! A fixed strict derivative bound excludes distinct coincidences on a
convex coordinate neighborhood. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem convex_injective_of_derivative_close
    {f : Base → ProjectionTarget 3} {L : Base →L[ℝ] ProjectionTarget 3}
    {K : NNReal} (hK : 0 < K) (hL : AntilipschitzWith K L)
    {S : Set Base} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hclose : ∀ x ∈ S, ‖fderiv ℝ f x-L‖ ≤ 1/(2*(K:ℝ))) :
    Set.InjOn f S := by
  intro x hx y hy he
  have hb := hS.norm_image_sub_le_of_norm_fderiv_le' hf hclose hx hy
  have hl := ZeroHomClass.bound_of_antilipschitz L hL (y-x)
  rw [he,sub_self,zero_sub,norm_neg] at hb
  have hKr : 0 < (K:ℝ) := hK
  have hnum : (K:ℝ)*(1/(2*(K:ℝ))) = 1/2 := by field_simp [ne_of_gt hKr]
  have hnorm : ‖y-x‖ ≤ (1/2)*‖y-x‖ := by
    calc
      ‖y-x‖ ≤ (K:ℝ)*‖L (y-x)‖ := hl
      _ ≤ (K:ℝ)*((1/(2*(K:ℝ)))*‖y-x‖) := mul_le_mul_of_nonneg_left hb hKr.le
      _ = (1/2)*‖y-x‖ := by rw [← mul_assoc,hnum]
  have hz : y-x = 0 := norm_eq_zero.mp (by linarith [norm_nonneg (y-x)])
  exact (sub_eq_zero.mp hz).symm

theorem exists_injective_coordinate_ball {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) {x : Base} (hi : Function.Injective (fderiv ℝ f x)) :
    ∃ K : NNReal, 0 < K ∧ AntilipschitzWith K (fderiv ℝ f x) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ y ∈ closedBall x r,
        ‖fderiv ℝ f y-fderiv ℝ f x‖ < 1/(4*(K:ℝ)) := by
  obtain ⟨K,hK,hL⟩ := (fderiv ℝ f x).toLinearMap.exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hi)
  have hp : 0 < 1/(4*(K:ℝ)) := by positivity
  have hn : ∀ᶠ y in 𝓝 x, ‖fderiv ℝ f y-fderiv ℝ f x‖ < 1/(4*(K:ℝ)) :=
    by
      simpa only [dist_eq_norm] using
        (Metric.tendsto_nhds.mp (hf.continuous_fderiv (by simp)).continuousAt) _ hp
  obtain ⟨r,hr,hrn⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨K,hK,hL,r/2,half_pos hr,?_⟩
  intro y hy
  apply hrn
  exact (closedBall_subset_ball (by linarith : r/2 < r)) hy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
