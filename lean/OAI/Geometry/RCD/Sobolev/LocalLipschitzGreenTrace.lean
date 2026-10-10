import OAI.Geometry.RCD.Sobolev.LipschitzGreenTrace
import OAI.Geometry.RCD.Sobolev.LocalLipschitzDerivative

namespace OAI

/-! # The local Green trace identity on the full open Euclidean ball -/

open Set Filter MeasureTheory Metric InnerProductSpace Laplacian
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem laplacian_zero_off_tsupport {n : ℕ} {ψ : Euclidean n → ℝ}
    (hψ : ContDiff ℝ 2 ψ) {x : Euclidean n} (hx : x∉tsupport ψ) : (Δ ψ) x=0 := by
  rw [laplacian_eq_sum_second_directional hψ]
  apply Finset.sum_eq_zero
  intro i _
  have hs : tsupport (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) ⊆ tsupport ψ :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))
  rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))]
  simp

theorem local_lipschitz_green_trace {n : ℕ} {f ψ : Euclidean n → ℝ}
    {S : ℝ} (hS : 0<S)
    (hf : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L f (closedBall 0 W))
    (hψ : InteriorSmoothTest n S ψ) :
    (∫ x, inner ℝ (gradient f x) (gradient ψ x))= -(∫ x, f x*(Δ ψ) x) := by
  obtain ⟨ρ,hρ,hsub⟩ := exists_pos_lt_subset_ball hS (isClosed_tsupport ψ) hψ.2.2
  let W := (ρ+S)/2
  have hW : 0<W := by dsimp only [W]; linarith [hρ.1]
  have hρW : ρ<W := by dsimp only [W]; linarith [hρ.2]
  have hWS : W<S := by dsimp only [W]; linarith [hρ.2]
  obtain ⟨L,hL⟩ := hf W hWS
  obtain ⟨G,hG,he⟩ := hL.extend_real
  have hpair := lipschitz_green_trace hG hS hψ
  have hvals (x : Euclidean n) :
      inner ℝ (gradient G x) (gradient ψ x)=inner ℝ (gradient f x) (gradient ψ x) ∧
      G x*(Δ ψ) x=f x*(Δ ψ) x := by
    by_cases hx : x∈tsupport ψ
    · have hxW : x∈ball (0:Euclidean n) W := (ball_subset_ball hρW.le) (hsub hx)
      have heq : G=ᶠ[𝓝 x] f := by
        filter_upwards [isOpen_ball.mem_nhds hxW] with y hy
        exact (he (ball_subset_closedBall hy)).symm
      exact ⟨by simp only [gradient,heq.fderiv_eq],by rw [heq.self_of_nhds]⟩
    · rw [show gradient ψ x=0 by simp only [gradient,fderiv_of_notMem_tsupport ℝ hx,map_zero],
        laplacian_zero_off_tsupport (hψ.1.of_le (by simp)) hx]
      simp
  rw [integral_congr_ae (Eventually.of_forall fun x => (hvals x).1),
    integral_congr_ae (Eventually.of_forall fun x => (hvals x).2)] at hpair
  exact hpair

end RegularPointCoordinates

end

end OAI
