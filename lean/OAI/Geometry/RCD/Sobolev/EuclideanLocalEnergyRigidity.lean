import OAI.Geometry.RCD.Sobolev.EuclideanConstantEnergyRigidity
import OAI.Geometry.RCD.Metric.EuclideanInteriorSmoothExtension

namespace OAI

/-! # Constant-energy rigidity on the whole open Euclidean ball -/

open Set Metric InnerProductSpace
open scoped ContDiff Topology
noncomputable section
namespace RegularPointCoordinates

theorem local_harmonic_constant_energy_affine {n : ℕ} {f : Euclidean n → ℝ}
    {S C : ℝ} (hS : 0 < S) (hf : ContDiffOn ℝ ∞ f (ball 0 S))
    (hh : HarmonicOnNhd f (ball 0 S))
    (he : ∀ y ∈ ball (0 : Euclidean n) S, ‖fderiv ℝ f y‖^2 = C) :
    ∀ x ∈ ball (0 : Euclidean n) S, f x = f 0 + fderiv ℝ f 0 x := by
  intro x hx
  have hxS : ‖x‖ < S := by simpa only [mem_ball,dist_zero_right] using hx
  let R := (‖x‖+S)/2
  have hR : 0 < R := by dsimp only [R]; linarith [norm_nonneg x]
  have hRS : R < S := by dsimp only [R]; linarith
  have hxR : x ∈ ball (0 : Euclidean n) R := by
    simp only [mem_ball,dist_zero_right]
    dsimp only [R]
    linarith
  obtain ⟨F,hF,hEq,hD⟩ := exists_interior_smooth_extension hR hRS hf
  have hH : HarmonicOnNhd F (ball 0 R) := by
    intro y hy
    apply (harmonicAt_congr_nhds (f₁ := F) (f₂ := f) ?_).mpr
    · exact hh y ((ball_subset_ball hRS.le) hy)
    · filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact hEq (ball_subset_closedBall hz)
  have hE : ∀ y ∈ ball (0 : Euclidean n) R, ‖fderiv ℝ F y‖^2 = C := by
    intro y hy
    rw [hD hy]
    exact he y ((ball_subset_ball hRS.le) hy)
  have hA := harmonic_constant_energy_affine (hF.1.of_le (by simp)) hR hH hE x hxR
  rw [hEq (ball_subset_closedBall hxR),hEq (ball_subset_closedBall (mem_ball_self hR)),
    hD (mem_ball_self hR)] at hA
  exact hA

end RegularPointCoordinates

end

end OAI
