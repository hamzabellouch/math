import OAI.Geometry.RCD.Sobolev.LipschitzCompactSubsequence

namespace OAI

/-! # Gluing compatible Lipschitz limits along a ball exhaustion -/

open Set Metric Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem glue_lipschitz_ball_limits {n : ℕ} {S : ℝ} (T : ℕ → ℝ)
    (hTS : ∀ m, T m<S) (hcofinal : ∀ ρ<S, ∃ m, ρ<T m)
    (G : ℕ → Euclidean n → ℝ) (L : ℕ → ℝ≥0)
    (hG : ∀ m, LipschitzWith (L m) (G m))
    (heq : ∀ i j, EqOn (G i) (G j) (ball 0 (min (T i) (T j)))) :
    ∃ g : Euclidean n → ℝ, ContinuousOn g (ball 0 S) ∧
      (∀ m, EqOn g (G m) (ball 0 (T m))) ∧
      (∀ ρ<S, ∃ C : ℝ≥0, LipschitzOnWith C g (closedBall 0 ρ)) ∧
      (∀ z, S≤‖z‖ → g z=0) := by
  classical
  let g : Euclidean n → ℝ := fun z =>
    if h : ∃ m, ‖z‖<T m then G (Nat.find h) z else 0
  have hgm (m : ℕ) : EqOn g (G m) (ball 0 (T m)) := by
    intro z hz
    have hz' : ‖z‖<T m := by simpa only [mem_ball,dist_zero_right] using hz
    have hex : ∃ j, ‖z‖<T j := ⟨m,hz'⟩
    dsimp only [g]
    rw [dite_eq_left hex]
    apply heq (Nat.find hex) m
    simpa only [mem_ball,dist_zero_right,lt_min_iff] using And.intro (Nat.find_spec hex) hz'
  refine ⟨g,?_,hgm,?_,?_⟩
  · intro z hz
    have hzS : ‖z‖<S := by simpa only [mem_ball,dist_zero_right] using hz
    obtain ⟨m,hm⟩ := hcofinal ‖z‖ hzS
    apply ContinuousAt.continuousWithinAt
    apply (hG m).continuous.continuousAt.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds (show z∈ball (0:Euclidean n) (T m) by
      simpa only [mem_ball,dist_zero_right] using hm)] with y hy
    exact hgm m hy
  · intro ρ hρ
    obtain ⟨m,hm⟩ := hcofinal ρ hρ
    refine ⟨L m,?_⟩
    intro x hx y hy
    have hx' : x∈ball (0:Euclidean n) (T m) := closedBall_subset_ball hm hx
    have hy' : y∈ball (0:Euclidean n) (T m) := closedBall_subset_ball hm hy
    rw [hgm m hx',hgm m hy']
    exact hG m x y
  · intro z hz
    have hn : ¬∃ m, ‖z‖<T m := by
      rintro ⟨m,hm⟩
      exact (not_lt_of_ge hz) (hm.trans (hTS m))
    exact dite_eq_right hn

end RegularPointCoordinates

end

end OAI
