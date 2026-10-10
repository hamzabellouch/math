import OAI.Geometry.RCD.Sobolev.LipschitzGreenPairing

namespace OAI

/-! # Compact-test Green pairing for locally Lipschitz open-ball limits -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem local_lipschitz_green_directional {n : ℕ} {f ψ : Euclidean n → ℝ}
    {S : ℝ} (hS : 0<S)
    (hf : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L f (closedBall 0 W))
    (hψ : InteriorSmoothTest n S ψ) (v : Euclidean n) :
    (∫ x, fderiv ℝ f x v*ψ x)= -(∫ x, f x*fderiv ℝ ψ x v) := by
  obtain ⟨ρ,hρ,hsub⟩ := exists_pos_lt_subset_ball hS (isClosed_tsupport ψ) hψ.2.2
  let W := (ρ+S)/2
  have hW : 0<W := by dsimp only [W]; linarith [hρ.1]
  have hρW : ρ<W := by dsimp only [W]; linarith [hρ.2]
  have hWS : W<S := by dsimp only [W]; linarith [hρ.2]
  obtain ⟨L,hL⟩ := hf W hWS
  obtain ⟨G,hG,he⟩ := hL.extend_real
  have hψW : InteriorSmoothTest n W ψ :=
    ⟨hψ.1,hψ.2.1,hsub.trans (ball_subset_ball hρW.le)⟩
  have hpair := lipschitz_green_directional hG hW hψW v
  have hvals (x : Euclidean n) :
      fderiv ℝ G x v*ψ x=fderiv ℝ f x v*ψ x ∧
      G x*fderiv ℝ ψ x v=f x*fderiv ℝ ψ x v := by
    by_cases hx : x∈tsupport ψ
    · have hxW : x∈ball (0:Euclidean n) W := (ball_subset_ball hρW.le) (hsub hx)
      have heq : G=ᶠ[𝓝 x] f := by
        filter_upwards [isOpen_ball.mem_nhds hxW] with y hy
        exact (he (ball_subset_closedBall hy)).symm
      exact ⟨by rw [heq.fderiv_eq],by rw [heq.self_of_nhds]⟩
    · rw [image_eq_zero_of_notMem_tsupport hx,fderiv_of_notMem_tsupport ℝ hx]
      simp
  rw [integral_congr_ae (Eventually.of_forall fun x => (hvals x).1),
    integral_congr_ae (Eventually.of_forall fun x => (hvals x).2)] at hpair
  exact hpair

end RegularPointCoordinates

end

end OAI
