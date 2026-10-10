import OAI.Analysis.CircleDomains.Topology.CircleIncrementContinuity

namespace OAI

/-! Uniform bounds for all initial lifts in a compact family of circle paths. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def circlePathPrefix (γ : C(unitInterval, UnitAddCircle)) (t : unitInterval) :
    C(unitInterval, UnitAddCircle) :=
  γ.comp ⟨fun s => s * t, continuous_id.mul continuous_const⟩

theorem continuous_circlePathPrefix :
    Continuous (fun p : C(unitInterval, UnitAddCircle) × unitInterval =>
      circlePathPrefix p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
    (continuous_snd.mul (continuous_snd.comp continuous_fst)))

theorem circlePathIncrement_prefix (γ : C(unitInterval, UnitAddCircle)) (t : unitInterval) :
    circlePathIncrement (circlePathPrefix γ t) =
      realCirclePathLift γ t - realCirclePathLift γ 0 := by
  let u := (realCirclePathLift γ).comp
    (⟨fun s : unitInterval => s * t, continuous_id.mul continuous_const⟩ :
      C(unitInterval, unitInterval))
  rw [circlePathIncrement_eq_lift (circlePathPrefix γ t) u
    (fun s => realCirclePathLift_projects γ (s * t))]
  simp only [u, ContinuousMap.comp_apply, ContinuousMap.coe_mk, one_mul, zero_mul]

theorem compact_circle_path_lifts_bounded
    (K : Set C(unitInterval, UnitAddCircle)) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ γ ∈ K, ∀ t : unitInterval, |realCirclePathLift γ t| ≤ M := by
  obtain ⟨M, hM⟩ := compact_circle_increment_bounded _
    ((hK.prod isCompact_univ).image continuous_circlePathPrefix)
  refine ⟨M + 1, fun γ hγ t => ?_⟩
  have hb : |realCirclePathLift γ t - realCirclePathLift γ 0| ≤ M := by
    rw [← circlePathIncrement_prefix]
    exact hM _ ⟨(γ, t), ⟨hγ, mem_univ _⟩, rfl⟩
  have hstart : realCirclePathLift γ 0 = circleRepresentative (γ 0) := by
    exact (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero _ _ _
  have hr := (AddCircle.equivIco (1 : ℝ) 0 (γ 0)).property
  have hs : |realCirclePathLift γ 0| ≤ 1 := by
    rw [hstart]
    change |((AddCircle.equivIco (1 : ℝ) 0 (γ 0)).val)| ≤ 1
    rw [abs_of_nonneg hr.1]
    simpa only [zero_add] using hr.2.le
  calc
    |realCirclePathLift γ t| =
        |(realCirclePathLift γ t - realCirclePathLift γ 0) + realCirclePathLift γ 0| := by
          congr 1; ring
    _ ≤ |realCirclePathLift γ t - realCirclePathLift γ 0| + |realCirclePathLift γ 0| := abs_add_le _ _
    _ ≤ M + 1 := add_le_add hb hs

end CircleDomainRigidity.FiniteTransfer

end

end OAI
