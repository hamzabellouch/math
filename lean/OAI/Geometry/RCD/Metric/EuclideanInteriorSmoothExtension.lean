import OAI.Geometry.RCD.Sobolev.EuclideanWeakHarmonicSmooth

namespace OAI

/-! # Compact smooth extensions on any strict interior ball -/

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
namespace RegularPointCoordinates

theorem exists_interior_smooth_extension {n : ℕ} {f : Euclidean n → ℝ} {R S : ℝ}
    (hR : 0<R) (hRS : R<S) (hf : ContDiffOn ℝ ∞ f (ball 0 S)) :
    ∃ F : Euclidean n → ℝ, InteriorSmoothTest n S F ∧
      EqOn F f (closedBall 0 R) ∧ EqOn (fderiv ℝ F) (fderiv ℝ f) (ball 0 R) := by
  let b := (R+S)/2
  have hRb : R<b := by dsimp only [b]; linarith
  have hbS : b<S := by dsimp only [b]; linarith
  let χ : ContDiffBump (0:Euclidean n) := ⟨R,b,hR,hRb⟩
  let F := fun x => χ x*f x
  have hs : tsupport (fun x => χ x)⊆ball (0:Euclidean n) S := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball hbS
  have hF : ContDiff ℝ ∞ F :=
    contDiff_mul_of_tsupport_subset isOpen_ball hf χ.contDiff hs
  have he : EqOn F f (closedBall 0 R) := by
    intro x hx
    change χ x*f x=f x
    rw [χ.one_of_mem_closedBall hx,one_mul]
  refine ⟨F,⟨hF,χ.hasCompactSupport.mul_right,tsupport_mul_subset_left.trans hs⟩,he,?_⟩
  intro x hx
  have heq : F=ᶠ[𝓝 x] f := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact he (ball_subset_closedBall hy)
  exact heq.fderiv_eq

end RegularPointCoordinates

end

end OAI
