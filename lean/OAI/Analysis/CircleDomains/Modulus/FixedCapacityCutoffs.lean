import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

namespace OAI

/-! Fixed smooth cutoffs for the scalar graph-capacity argument. Their
bounds are independent of the function, graph point, and chosen scale. -/
open Set Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def scalarCapacityBump : ContDiffBump (0 : ℝ) := ⟨1,2,zero_lt_one,one_lt_two⟩
def spatialCapacityBump : ContDiffBump (0 : EuclideanPlane) := ⟨2,4,by norm_num,by norm_num⟩

lemma euclideanPlane_norm_le_two_of_coordinate_unit {x : EuclideanPlane}
    (hx : euclideanPlaneCoordinates x ∈ closedBall 0 1) : ‖x‖ ≤ 2 := by
  have hp : |x 0| ≤ 1 ∧ |x 1| ≤ 1 := by
    simpa only [mem_closedBall, euclideanPlaneCoordinates_apply, Prod.dist_eq,
      Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero, max_le_iff] using hx
  have he : ‖x‖^2 = (x 0)^2+(x 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
  have h0 : (x 0)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg (x 0)) zero_le_one).mpr hp.1
  have h1 : (x 1)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg (x 1)) zero_le_one).mpr hp.2
  nlinarith [norm_nonneg x]

lemma scalarCapacityBump_one {t : ℝ} (ht : |t| ≤ 1) : scalarCapacityBump t = 1 := by
  apply scalarCapacityBump.one_of_mem_closedBall
  simpa only [scalarCapacityBump, mem_closedBall, Real.dist_eq, sub_zero] using ht

lemma spatialCapacityBump_one {x : EuclideanPlane}
    (hx : euclideanPlaneCoordinates x ∈ closedBall 0 1) : spatialCapacityBump x = 1 := by
  apply spatialCapacityBump.one_of_mem_closedBall
  simpa only [spatialCapacityBump, mem_closedBall, dist_zero_right] using
    euclideanPlane_norm_le_two_of_coordinate_unit hx

lemma scalarCapacityBump_zero {t : ℝ} (ht : 2 < |t|) :
    scalarCapacityBump t = 0 ∧ deriv scalarCapacityBump t = 0 := by
  have hn : t ∉ tsupport (scalarCapacityBump : ℝ → ℝ) := by
    rw [scalarCapacityBump.tsupport_eq]
    simpa only [scalarCapacityBump, mem_closedBall, Real.dist_eq, sub_zero, not_le] using ht
  exact ⟨image_eq_zero_of_notMem_tsupport hn,
    image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_deriv_subset h))⟩

lemma spatialCapacityBump_zero {x : EuclideanPlane} (hx : 4 < ‖x‖) :
    spatialCapacityBump x = 0 ∧ fderiv ℝ spatialCapacityBump x = 0 := by
  have hn : x ∉ tsupport (spatialCapacityBump : EuclideanPlane → ℝ) := by
    rw [spatialCapacityBump.tsupport_eq]
    simpa only [spatialCapacityBump, mem_closedBall, dist_zero_right, not_le] using hx
  exact ⟨image_eq_zero_of_notMem_tsupport hn,
    image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_fderiv_subset ℝ h))⟩

lemma exists_capacity_cutoff_derivative_bound : ∃ C : ℝ, 0 ≤ C ∧
    (∀ t, ‖deriv scalarCapacityBump t‖ ≤ C) ∧
    (∀ x, ‖fderiv ℝ spatialCapacityBump x‖ ≤ C) := by
  obtain ⟨A,hA⟩ := ((scalarCapacityBump.contDiff : ContDiff ℝ 1 (scalarCapacityBump : ℝ → ℝ)).continuous_deriv le_rfl).bounded_above_of_compact_support
    scalarCapacityBump.hasCompactSupport.deriv
  obtain ⟨B,hB⟩ := ((spatialCapacityBump.contDiff : ContDiff ℝ 1 (spatialCapacityBump : EuclideanPlane → ℝ)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (spatialCapacityBump.hasCompactSupport.fderiv ℝ)
  exact ⟨max 0 (max A B),le_max_left _ _,
    fun t => (hA t).trans ((le_max_left _ _).trans (le_max_right _ _)),
    fun x => (hB x).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

end CircleDomainRigidity

end

end OAI
