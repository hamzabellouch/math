import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricCoarseBridge
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

/-!
# Linear metric chains and coarse Lipschitz bounds

An explicit large-scale geodesic condition allows one to sum local bounds
along a chain. For continuous homomorphisms out of proper metric groups,
the local bound comes from compactness. This is the elementary metric step
in the proper cocompact homomorphism form of the Milnor--Švarc argument.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

/-- Chains joining any two points with bounded step size and a linear bound
on the number of steps, including their vertices and endpoint identities. -/
structure LinearMetricChains (X : Type*) [PseudoMetricSpace X] where
  step : ℝ
  step_pos : 0 < step
  slope : ℝ
  slope_nonneg : 0 ≤ slope
  error : ℝ
  error_nonneg : 0 ≤ error
  chain : ∀ x y : X, ∃ (n : ℕ) (p : ℕ → X),
    p 0 = x ∧ p n = y ∧ (n : ℝ) ≤ slope * dist x y + error ∧
      ∀ i < n, dist (p i) (p (i + 1)) ≤ step

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A uniform bound on single steps becomes an affine metric bound by
summing along the actual chains. -/
theorem LinearMetricChains.coarseLipschitz (C : LinearMetricChains X) (f : X → Y)
    {D : ℝ} (hD : 0 ≤ D)
    (hstep : ∀ x y, dist x y ≤ C.step → dist (f x) (f y) ≤ D) :
    ∀ x y, dist (f x) (f y) ≤ (D * C.slope) * dist x y + D * C.error := by
  intro x y
  obtain ⟨n, p, hp0, hpn, hn, hp⟩ := C.chain x y
  have hdist : dist (f (p 0)) (f (p n)) ≤ (n : ℝ) * D := by
    calc
      dist (f (p 0)) (f (p n)) ≤
          ∑ i ∈ Finset.range n, dist (f (p i)) (f (p (i + 1))) :=
        dist_le_range_sum_dist (f ∘ p) n
      _ ≤ ∑ _i ∈ Finset.range n, D := by
        exact Finset.sum_le_sum (fun i hi => hstep _ _ (hp i (Finset.mem_range.mp hi)))
      _ = (n : ℝ) * D := by simp
  rw [hp0, hpn] at hdist
  calc
    dist (f x) (f y) ≤ (n : ℝ) * D := hdist
    _ ≤ (C.slope * dist x y + C.error) * D := mul_le_mul_of_nonneg_right hn hD
    _ = (D * C.slope) * dist x y + D * C.error := by ring

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul G G] [IsIsometricSMul H H]

/-- A continuous homomorphism out of a proper metric group has uniformly
bounded image displacement on any bounded source step. -/
theorem continuousHom_bounded_metric_steps [ProperSpace G]
    (f : G →* H) (hf : Continuous f) (R : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y, dist x y ≤ R → dist (f x) (f y) ≤ D := by
  obtain ⟨D, hD⟩ := (isCompact_closedBall (1 : G) R).bddAbove_image
    (continuous_const.dist hf).continuousOn
  refine ⟨max D 0, le_max_right _ _, fun x y hxy => ?_⟩
  have hmem : x⁻¹ * y ∈ closedBall (1 : G) R := by
    simpa only [mem_closedBall, dist_comm (x⁻¹ * y), dist_one_groupDifference] using hxy
  have hb : dist (1 : H) (f (x⁻¹ * y)) ≤ D := hD (mem_image_of_mem _ hmem)
  rw [map_mul, map_inv, dist_one_groupDifference] at hb
  exact hb.trans (le_max_left _ _)

/-- The homomorphism's affine bound requires only compactness and the
explicit linear chains; no global differentiability estimate is needed. -/
theorem continuousHom_coarseLipschitz [ProperSpace G] (C : LinearMetricChains G)
    (f : G →* H) (hf : Continuous f) :
    ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
      ∀ x y, dist (f x) (f y) ≤ K * dist x y + B := by
  obtain ⟨D, hD, hstep⟩ := continuousHom_bounded_metric_steps f hf C.step
  exact ⟨D * C.slope, D * C.error,
    mul_nonneg hD C.slope_nonneg, mul_nonneg hD C.error_nonneg,
    C.coarseLipschitz f hD hstep⟩

end PolycyclicRecognition

end

end OAI
