import OAI.Geometry.RCD.Sobolev.EuclideanReflectedLaplacian
import OAI.Geometry.RCD.Sobolev.InteriorSmoothTestBounds

namespace OAI

/-! # Smooth harmonic local averages of a distributional harmonic function -/

open Set Metric Filter MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff Convolution Topology
noncomputable section
namespace RegularPointCoordinates

/-- The compact-test distributional Laplace equation on one Euclidean ball. -/
def EuclideanWeakHarmonicOn {n : ℕ} (g : Euclidean n → ℝ) (S : ℝ) : Prop :=
  ∀ ψ : Euclidean n → ℝ, InteriorSmoothTest n S ψ → ∫ y, g y*(Δ ψ) y=0

theorem weak_harmonic_convolution {n : ℕ} {f k : Euclidean n → ℝ} {S r : ℝ}
    (hf : LocallyIntegrable f volume) (hk : ContDiff ℝ ∞ k) (hks : HasCompactSupport k)
    (hkr : tsupport k⊆closedBall 0 r) (hweak : EuclideanWeakHarmonicOn f S) :
    HarmonicOnNhd (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] k) (ball 0 (S-r)) := by
  have hsmooth := hks.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hk
  have hlap (x : Euclidean n) (hx : x∈ball 0 (S-r)) :
      (Δ (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] k)) x=0 := by
    let ψ := fun y => k (x-y)
    have hψ : ContDiff ℝ ∞ ψ := hk.comp (contDiff_const.sub contDiff_id)
    have hsupport : tsupport ψ⊆closedBall x r := by
      apply closure_minimal _ isClosed_closedBall
      intro y hy
      have hxy := hkr (subset_tsupport k hy)
      rw [mem_closedBall,dist_zero_right] at hxy
      rw [mem_closedBall,dist_comm,dist_eq_norm]
      exact hxy
    have hcompact : HasCompactSupport ψ :=
      (isCompact_closedBall x r).of_isClosed_subset (isClosed_tsupport _) hsupport
    have hsub : tsupport ψ⊆ball 0 S := by
      intro y hy
      have hyr : dist y x≤r := hsupport hy
      have hxS : ‖x‖<S-r := by simpa only [mem_ball,dist_zero_right] using hx
      have ht := dist_triangle y x 0
      simp only [dist_zero_right] at ht
      simpa only [mem_ball,dist_zero_right] using (show ‖y‖<S by linarith)
    have he := hweak ψ ⟨hψ,hcompact,hsub⟩
    rw [laplacian_comp_const_sub (hk.of_le (by simp)) x] at he
    rw [scalar_convolution_laplacian hf (hk.of_le (by simp)) hks,convolution_def]
    exact he
  intro x hx
  refine ⟨(hsmooth.of_le (by simp)).contDiffAt,?_⟩
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact hlap y hy

end RegularPointCoordinates

end

end OAI
