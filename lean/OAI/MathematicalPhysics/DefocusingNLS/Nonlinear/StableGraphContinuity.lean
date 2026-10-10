import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphContraction
import Mathlib.Topology.UniformSpace.UniformApproximation

namespace OAI

/-! # Continuity from uniformly contracting iterates

Only continuity of the observed finite iterates is required.  In the stable
graph application the observation is a single coordinate, whose continuity
comes from strong Fourier continuity and uniformly convergent backward tails.
Operator-norm continuity of the free Schrödinger group is unnecessary.
-/

open Filter Topology

open scoped BoundedContinuousFunction

namespace DefocusingNLS

theorem continuous_contraction_observation
    {P X Y : Type*} [TopologicalSpace P] [NormedAddCommGroup X] [PseudoMetricSpace Y]
    (T : P → X → X) (z : P → X) (observe : X → Y)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hmap : ∀ p x, ‖x‖ ≤ ρ → ‖T p x‖ ≤ ρ)
    (hcontract : ∀ p x y, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      dist (T p x) (T p y) ≤ (1 / 2 : ℝ) * dist x y)
    (hz : ∀ p, T p (z p) = z p) (hzbound : ∀ p, ‖z p‖ ≤ ρ)
    (hobserve : ∀ x y, dist (observe x) (observe y) ≤ dist x y)
    (hiterate : ∀ n : ℕ, Continuous (fun p => observe ((T p)^[n] 0))) :
    Continuous (fun p => observe (z p)) := by
  have hi : ∀ n : ℕ, ∀ p : P, ‖(T p)^[n] 0‖ ≤ ρ ∧
      dist ((T p)^[n] 0) (z p) ≤ (1 / 2 : ℝ) ^ n * ρ := by
    intro n
    induction n with
    | zero =>
        intro p
        simpa only [Function.iterate_zero_apply, norm_zero, dist_zero_left, pow_zero,
          one_mul] using And.intro hρ (hzbound p)
    | succ n ih =>
        intro p
        obtain ⟨hnorm, hdist⟩ := ih p
        rw [Function.iterate_succ_apply']
        refine ⟨hmap p _ hnorm, ?_⟩
        calc
          dist (T p ((T p)^[n] 0)) (z p) =
              dist (T p ((T p)^[n] 0)) (T p (z p)) := by rw [hz]
          _ ≤ (1 / 2 : ℝ) * dist ((T p)^[n] 0) (z p) :=
            hcontract p _ _ hnorm (hzbound p)
          _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * ρ) :=
            mul_le_mul_of_nonneg_left hdist (by norm_num)
          _ = (1 / 2 : ℝ) ^ (n + 1) * ρ := by rw [pow_succ]; ring
  have ht : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * ρ) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ρ
  have hu : TendstoUniformly (fun n p => observe ((T p)^[n] 0))
      (fun p => observe (z p)) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn p
    calc
      dist (observe (z p)) (observe ((T p)^[n] 0)) ≤ dist (z p) ((T p)^[n] 0) :=
        hobserve _ _
      _ = dist ((T p)^[n] 0) (z p) := dist_comm _ _
      _ ≤ (1 / 2 : ℝ) ^ n * ρ := (hi n p).2
      _ < ε := hn
  exact hu.continuous (Eventually.of_forall hiterate).frequently

end DefocusingNLS

end OAI
