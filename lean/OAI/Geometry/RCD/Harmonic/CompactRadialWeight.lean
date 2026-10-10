import OAI.Geometry.RCD.Sobolev.WeakHarmonicRadialPairing
import OAI.Geometry.RCD.Metric.EuclideanInteriorSmoothExtension

namespace OAI

/-! # A compact nonnegative weight equal to half the squared radius -/

open Set Metric Filter MeasureTheory
open scoped BoundedContinuousFunction Topology ContDiff
noncomputable section
namespace RegularPointCoordinates

theorem exists_compact_radial_weight {n : ℕ} {T S : ℝ} (hT : 0<T) (hTS : T<S) :
    ∃ F : Euclidean n →ᵇ ℝ, InteriorSmoothTest n S F ∧ (∀ x, 0≤F x) ∧
      EqOn F (fun x => ‖x‖^2/2) (closedBall 0 T) ∧
      ∀ x∈ball (0:Euclidean n) T, gradient F x=x := by
  let b := (T+S)/2
  have hTb : T<b := by dsimp only [b]; linarith
  have hbS : b<S := by dsimp only [b]; linarith
  let χ : ContDiffBump (0:Euclidean n) := ⟨T,b,hT,hTb⟩
  let G := fun x : Euclidean n => χ x*(‖x‖^2/2)
  have hG : InteriorSmoothTest n S G := by
    refine ⟨χ.contDiff.mul ((contDiff_id.norm_sq ℝ).div_const 2),χ.hasCompactSupport.mul_right,?_⟩
    exact tsupport_mul_subset_left.trans ((by rw [χ.tsupport_eq]; exact closedBall_subset_ball hbS))
  obtain ⟨C,hC⟩ := hG.2.1.exists_bound_of_continuous hG.1.continuous
  let F : Euclidean n →ᵇ ℝ := ⟨⟨G,hG.1.continuous⟩,2*C,by
    intro x y
    rw [Real.dist_eq]
    have hx : |G x|≤C := by simpa only [Real.norm_eq_abs] using hC x
    have hy : |G y|≤C := by simpa only [Real.norm_eq_abs] using hC y
    exact (abs_sub (G x) (G y)).trans (by linarith)⟩
  have he : EqOn F (fun x => ‖x‖^2/2) (closedBall 0 T) := by
    intro x hx
    change χ x*(‖x‖^2/2)=‖x‖^2/2
    rw [χ.one_of_mem_closedBall hx,one_mul]
  refine ⟨F,hG,fun x => mul_nonneg χ.nonneg (div_nonneg (sq_nonneg _) (by norm_num)),he,?_⟩
  intro x hx
  have heq : (F : Euclidean n → ℝ)=ᶠ[𝓝 x] (fun y => ‖y‖^2/2) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact he (ball_subset_closedBall hy)
  rw [show gradient F x=gradient (fun y : Euclidean n => ‖y‖^2/2) x by
    simp only [gradient,heq.fderiv_eq]]
  exact gradient_half_norm_sq x

end RegularPointCoordinates

end

end OAI
