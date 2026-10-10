import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricQuasiEquivalence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseEquivalence

namespace OAI

/-! # Passing from finite-difference control to metric coarse inverses -/

noncomputable section
namespace PolycyclicRecognition

open Metric Set

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul G G] [IsIsometricSMul H H]

theorem GroupBornologous.bounded_metric_steps {f : G → H}
    (hf : GroupBornologous f)
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite) (R : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y, dist x y ≤ R → dist (f x) (f y) ≤ D := by
  obtain ⟨T, hT, hmap⟩ := hf _ (hfinite R)
  obtain ⟨D, hD⟩ := hT.isBounded.subset_closedBall (1 : H)
  refine ⟨max D 0, le_max_right _ _, fun x y hxy => ?_⟩
  have hx : x⁻¹ * y ∈ closedBall (1 : G) R := by
    simpa only [mem_closedBall, dist_comm (x⁻¹ * y), dist_one_groupDifference] using hxy
  have hd := hD (hmap x y hx)
  rw [mem_closedBall, dist_comm, dist_one_groupDifference] at hd
  exact hd.trans (le_max_left _ _)

theorem GroupBornologous.coarseLipschitz {f : G → H}
    (hf : GroupBornologous f) (C : LinearMetricChains G)
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite) :
    ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧
      ∀ x y, dist (f x) (f y) ≤ K * dist x y + B := by
  obtain ⟨D, hD, hstep⟩ := hf.bounded_metric_steps hfinite C.step
  exact ⟨D * C.slope, D * C.error, mul_nonneg hD C.slope_nonneg,
    mul_nonneg hD C.error_nonneg, C.coarseLipschitz f hD hstep⟩

theorem finite_groupDifference_bounded_error {r : G → G}
    (hr : (range fun x => x⁻¹ * r x).Finite) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x, dist x (r x) ≤ E := by
  obtain ⟨E, hE⟩ := hr.isBounded.subset_closedBall (1 : G)
  refine ⟨max E 0, le_max_right _ _, fun x => ?_⟩
  have hx := hE (mem_range_self x)
  rw [mem_closedBall, dist_comm, dist_one_groupDifference] at hx
  exact hx.trans (le_max_left _ _)

/-- On metrics with linear chains and finite balls, an actual discrete
coarse equivalence is a metric quasi-equivalence. -/
def GroupCoarseEquivalence.metric (e : GroupCoarseEquivalence G H)
    (CG : LinearMetricChains G) (CH : LinearMetricChains H)
    (hG : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (hH : ∀ R : ℝ, (closedBall (1 : H) R).Finite) : MetricQuasiEquivalence G H where
  toFun := e.toFun
  invFun := e.invFun
  toFun_control := e.bornologous_toFun.coarseLipschitz CG hG
  invFun_control := e.bornologous_invFun.coarseLipschitz CH hH
  left_close := finite_groupDifference_bounded_error e.left_error
  right_close := finite_groupDifference_bounded_error e.right_error

/-- An isomorphism is also a discrete coarse equivalence, with exact inverses. -/
def MulEquiv.groupCoarseEquivalence (e : G ≃* H) : GroupCoarseEquivalence G H where
  toFun := e
  invFun := e.symm
  bornologous_toFun := groupBornologous_hom e.toMonoidHom
  bornologous_invFun := groupBornologous_hom e.symm.toMonoidHom
  left_error := by simp
  right_error := by simp

end PolycyclicRecognition

end

end OAI
