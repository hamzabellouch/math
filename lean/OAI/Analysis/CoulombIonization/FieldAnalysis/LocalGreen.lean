import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombTestCharge

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis

lemma local_laplacian_green_ball {f g : TFSpace → ℝ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : ∀ x ∈ ball (0 : TFSpace) R, ContDiffAt ℝ 2 f x)
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (hs : tsupport g ⊆ ball 0 r) :
    (∫ x, f x*Δ g x) = ∫ x, Δ f x*g x := by
  let b : ContDiffBump (0 : TFSpace) := ⟨r,(r+R)/2,hr,by linarith⟩
  let F : TFSpace → ℝ := fun x => b x*f x
  have hbR : b.rOut < R := by dsimp [b]; linarith
  have hF : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball (0 : TFSpace) R
    · exact b.contDiffAt.mul (hf x hx)
    · have hnx : b.rOut < ‖x‖ := hbR.trans_le (le_of_not_gt (by
        simpa only [mem_ball,dist_zero_right] using hx))
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [continuous_norm.continuousAt.eventually (Ioi_mem_nhds hnx)] with z hz
      simp only [F,b.zero_of_le_dist (by simpa only [dist_zero_right] using hz.le),zero_mul]
  have he {x : TFSpace} (hx : x ∈ ball 0 r) : F =ᶠ[𝓝 x] f := by
    have hn : ‖x‖ < b.rIn := by simpa only [mem_ball,dist_zero_right] using hx
    filter_upwards [continuous_norm.continuousAt.eventually (Iio_mem_nhds hn)] with z hz
    simp only [F,b.one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right] using hz.le),one_mul]
  calc
    _ = ∫ x, F x*Δ g x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : Δ g x = 0
        · simp only [hx,mul_zero]
        · change f x * Δ g x = F x * Δ g x
          rw [(he (hs (tfLaplacian_support hg hx))).eq_of_nhds]
    _ = ∫ x, Δ F x*g x := compact_laplacian_green hF hg hcg
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : g x = 0
        · simp only [hx,mul_zero]
        · change Δ F x * g x = Δ f x * g x
          rw [(laplacian_congr_nhds (he (hs (subset_tsupport g hx)))).eq_of_nhds]

end CoulombAnalysis

end

end OAI
