import OAI.Geometry.RCD.Metric.BallLimitGluing

namespace OAI

/-! # Compatible local Lipschitz limits on all of Euclidean space -/

open Set Metric Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem glue_exhausting_lipschitz_balls {n : ℕ} (T : ℕ → ℝ)
    (hT : Tendsto T atTop atTop) (G : ℕ → Euclidean n → ℝ) (L : ℕ → ℝ≥0)
    (hG : ∀ m, LipschitzWith (L m) (G m))
    (heq : ∀ i j, EqOn (G i) (G j) (ball 0 (min (T i) (T j)))) :
    ∃ g : Euclidean n → ℝ, Continuous g ∧
      (∀ m, EqOn g (G m) (ball 0 (T m))) ∧
      ∀ ρ : ℝ, ∃ C : ℝ≥0, LipschitzOnWith C g (closedBall 0 ρ) := by
  classical
  have hcover (z : Euclidean n) : ∃ m, ‖z‖ < T m :=
    (hT.eventually_gt_atTop ‖z‖).exists
  let g : Euclidean n → ℝ := fun z => G (Nat.find (hcover z)) z
  have hgm (m : ℕ) : EqOn g (G m) (ball 0 (T m)) := by
    intro z hz
    apply heq (Nat.find (hcover z)) m
    simpa only [mem_ball,dist_zero_right,lt_min_iff] using
      And.intro (Nat.find_spec (hcover z))
        (by simpa only [mem_ball,dist_zero_right] using hz : ‖z‖ < T m)
  refine ⟨g,?_,hgm,?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro z
    obtain ⟨m,hm⟩ := hcover z
    apply (hG m).continuous.continuousAt.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds (show z ∈ ball (0 : Euclidean n) (T m) by
      simpa only [mem_ball,dist_zero_right] using hm)]
      with y hy
    exact hgm m hy
  · intro ρ
    obtain ⟨m,hm⟩ := (hT.eventually_gt_atTop ρ).exists
    refine ⟨L m,?_⟩
    intro x hx y hy
    rw [hgm m (closedBall_subset_ball hm hx),hgm m (closedBall_subset_ball hm hy)]
    exact hG m x y

end RegularPointCoordinates

end

end OAI
