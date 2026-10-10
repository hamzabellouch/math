import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLocalL2
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedFlow

namespace OAI

/-! # Weakly null data have vanishing local observation

This is the compact observation step in the time-one semigroup argument.
Weak convergence is stated using bounded real-linear functionals, matching
the real-linear Schrödinger linearization.
-/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_homogeneousLocalObservation_of_weakNull (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (S : Set E) [CompactSpace S]
    (u : ℕ → HomogeneousY a k) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousLocalObservation a k ha ha1 hk S (u n))
      atTop (𝓝 0) := by
  let T := homogeneousLocalObservation a k ha ha1 hk S
  have hc := (isCompactOperator_homogeneousLocalObservation a k ha ha1 hk S).isCompact_closure_image_closedBall M
  apply hc.tendsto_nhds_of_unique_mapClusterPt
  · exact Filter.Eventually.of_forall (fun n => subset_closure
      ⟨u n, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu n, rfl⟩)
  · intro g _hg hcluster
    apply BoundedContinuousFunction.ext
    intro x
    have heval : MapClusterPt (g x) atTop (fun n => T (u n) x) :=
      hcluster.continuousAt_comp (BoundedContinuousFunction.evalCLM ℂ x).continuous.continuousAt
    have hzero : Tendsto (fun n => T (u n) x) atTop (𝓝 0) :=
      hweak ((homogeneousPointEvaluation a k ha ha1 hk x).restrictScalars ℝ)
    exact eq_of_nhds_neBot (heval.clusterPt.mono hzero)

theorem tendsto_homogeneousLocalL2Observation_of_weakNull (a k R M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u : ℕ → HomogeneousY a k) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousLocalL2Observation a k R ha ha1 hk (u n))
      atTop (𝓝 0) := by
  have ht := tendsto_homogeneousLocalObservation_of_weakNull a k M ha ha1 hk
    (Metric.closedBall 0 R) u hu hweak
  let J : BoundedContinuousFunction (Metric.closedBall (0 : E) R) ℂ →L[ℂ]
      Lp ℂ 2 (homogeneousBallMeasure R) :=
    BoundedContinuousFunction.toLp 2 (homogeneousBallMeasure R) ℂ
  have hc := J.continuous.tendsto 0
  simpa only [Function.comp_def, map_zero, homogeneousLocalL2Observation,
    ContinuousLinearMap.comp_apply, J] using hc.comp ht

/-- At each fixed time the actual linearized evolution preserves weak nullity,
so its local observation converges strongly to zero. -/
theorem tendsto_homogeneousLinearized_localL2_of_weakNull (a b k T R M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (q : HomogeneousY a k) (t : Icc (0 : ℝ) T)
    (u : ℕ → HomogeneousY a k) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousLocalL2Observation a k R ha ha1 hk
      (homogeneousLinearizedPropagator a b k T ha ha1 hk hT m q (u n) t))
      atTop (𝓝 0) := by
  let V : HomogeneousY a k →L[ℝ] HomogeneousY a k :=
    (ContinuousMap.evalCLM (R := ℝ) t).comp
      (homogeneousLinearizedPropagator a b k T ha ha1 hk hT m q)
  apply tendsto_homogeneousLocalL2Observation_of_weakNull a k R (‖V‖ * M)
    ha ha1 hk (fun n => V (u n))
  · intro n
    exact (V.le_opNorm (u n)).trans (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg V))
  · intro ℓ
    exact hweak (ℓ.comp V)

end DefocusingNLS

end OAI
