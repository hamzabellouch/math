import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences

namespace OAI

/-! # Extending scalar convergence from dense times

Uniform local Lipschitz bounds turn convergence at a fixed dense sequence
of times into convergence at every time, with a continuous limit.
-/

open Set Filter Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {T : Type*} [MetricSpace T]

theorem local_lipschitz_cauchy_of_dense (F : ℕ → T → ℝ) (s : ℕ → T)
    (hs : DenseRange s)
    (hL : ∀ t, ∃ (L : ℝ≥0) (r : ℝ), 0 < r ∧
      ∀ k, LipschitzOnWith L (F k) (ball t r))
    (hC : ∀ j, CauchySeq (fun k => F k (s j))) (t : T) :
    CauchySeq (fun k => F k t) := by
  obtain ⟨L,r,hr,hL⟩ := hL t
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let η := min (r/2) (ε/(8*((L:ℝ)+1)))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  obtain ⟨j,hj⟩ := hs.exists_dist_lt t hη
  have hsj : s j ∈ ball t r := by
    rw [mem_ball,dist_comm]
    exact hj.trans (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have ht : t ∈ ball t r := mem_ball_self hr
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hC j) (ε/2) (half_pos hε)
  refine ⟨N,fun a ha b hb => ?_⟩
  have hsmall : (L:ℝ)*dist t (s j) < ε/8 := by
    have hj' : dist t (s j) < ε/(8*((L:ℝ)+1)) := hj.trans_le (min_le_right _ _)
    have he := (lt_div_iff₀ (show 0 < 8*((L:ℝ)+1) by positivity)).mp hj'
    nlinarith [dist_nonneg (x := t) (y := s j)]
  have ha' := (hL a).dist_le_mul t ht (s j) hsj
  have hb' := (hL b).dist_le_mul t ht (s j) hsj
  have hmid := hN a ha b hb
  have htri := dist_triangle4 (F a t) (F a (s j)) (F b (s j)) (F b t)
  rw [dist_comm (F b (s j))] at htri
  linarith

theorem local_lipschitz_limit_of_dense (F : ℕ → T → ℝ) (s : ℕ → T)
    (hs : DenseRange s)
    (hL : ∀ t, ∃ (L : ℝ≥0) (r : ℝ), 0 < r ∧
      ∀ k, LipschitzOnWith L (F k) (ball t r))
    (hC : ∀ j, CauchySeq (fun k => F k (s j))) :
    ∃ f : T → ℝ, Continuous f ∧ ∀ t, Tendsto (fun k => F k t) atTop (𝓝 (f t)) := by
  let f t := limUnder atTop (fun k => F k t)
  have hf t : Tendsto (fun k => F k t) atTop (𝓝 (f t)) :=
    (local_lipschitz_cauchy_of_dense F s hs hL hC t).tendsto_limUnder
  refine ⟨f,continuous_iff_continuousAt.mpr (fun t => ?_),hf⟩
  obtain ⟨L,r,hr,hL⟩ := hL t
  have hfl : LipschitzOnWith L f (ball t r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto ((hf x).dist (hf y))
      (Eventually.of_forall fun k => (hL k).dist_le_mul x hx y hy)
  exact (hfl.continuousOn t (mem_ball_self hr)).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))

end RegularPointCoordinates

end

end OAI
