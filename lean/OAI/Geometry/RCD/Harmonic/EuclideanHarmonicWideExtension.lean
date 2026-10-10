import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicCompactExtension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace OAI

/-! # A compact extension with fixed room around the half ball -/

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped ContDiff Topology

noncomputable section
namespace RegularPointCoordinates

/-- A C² compact extension equal to the harmonic model on the three-quarter
ball; this leaves fixed room for a mean kernel around every half-ball point. -/
theorem EuclideanHarmonicModel.wide_compact_extension {n : ℕ} {S : ℝ}
    (w : EuclideanHarmonicModel n S) (hS : 0 < S) :
    ∃ F : Euclidean n → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      tsupport F ⊆ closedBall 0 (7*S/8) ∧
      (∀ x ∈ ball (0 : Euclidean n) (3*S/4), F x = w.value x) ∧
      (∀ x, |F x| ≤ |w.value x|) ∧
      HarmonicOnNhd F (ball 0 (3*S/4)) := by
  let χ : ContDiffBump (0 : Euclidean n) :=
    { rIn := 3*S/4, rOut := 7*S/8, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hs : tsupport (χ : Euclidean n → ℝ) ⊆ ball 0 S := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by dsimp only [χ]; linarith)
  let F := fun x => χ x*w.value x
  have hF : ContDiff ℝ 2 F :=
    contDiff_mul_of_tsupport_subset isOpen_ball w.harmonic.contDiffOn χ.contDiff hs
  have hFs : tsupport F ⊆ closedBall 0 (7*S/8) := by
    exact tsupport_mul_subset_left.trans (by rw [χ.tsupport_eq])
  have he (x : Euclidean n) (hx : x ∈ ball 0 (3*S/4)) : F x = w.value x := by
    have hh : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall.mpr (le_of_lt hx))
    change χ x*w.value x = w.value x
    rw [hh,one_mul]
  refine ⟨F,hF,(isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hFs,hFs,he,?_,?_⟩
  · intro x
    change |χ x*w.value x| ≤ |w.value x|
    rw [abs_mul,abs_of_nonneg χ.nonneg]
    exact mul_le_of_le_one_left (abs_nonneg _) χ.le_one
  · intro x hx
    apply (harmonicAt_congr_nhds (f₁ := F) (f₂ := w.value) ?_).mpr
    · exact w.harmonic x ((ball_subset_ball (by linarith : 3*S/4 ≤ S)) hx)
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact he y hy

end RegularPointCoordinates

end

end OAI
