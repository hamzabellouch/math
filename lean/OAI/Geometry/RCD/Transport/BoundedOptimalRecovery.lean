import OAI.Geometry.RCD.Transport.DominatedOptimalPlan

namespace OAI

/-! # Bounded optimal recovery of an arbitrary finite-cost geodesic plan

Cutting off the original plan preserves optimality for the resulting
endpoint marginals. All integrable moments converge along the recovery.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [SeparableSpace X] in
theorem bounded_optimal_recovery
    (ρ : ProbabilityMeasure C(Time,X)) (p : X)
    (hg : ∀ᵐ γ ∂(ρ : Measure C(Time,X)), IsGeodesic γ)
    (hp : IsOptimalCoupling ((ρ : Measure C(Time,X)).map (fun γ => γ 0))
      ((ρ : Measure C(Time,X)).map (fun γ => γ 1))
      ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))))
    (hc : transportCost ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))≠∞) :
    ∃ (ρs : ℕ → ProbabilityMeasure C(Time,X)) (R : ℕ → ℝ),
      (∀ j, 0≤R j) ∧
      (∀ j, (ρs j : Measure C(Time,X))≤(2 : ℝ≥0∞) • (ρ : Measure C(Time,X))) ∧
      (∀ j, ∀ᵐ γ ∂(ρs j : Measure C(Time,X)), IsGeodesic γ) ∧
      (∀ j, ∀ᵐ γ ∂(ρs j : Measure C(Time,X)), ∀ t : Time, dist (γ t) p≤R j) ∧
      (∀ j, IsOptimalCoupling ((ρs j : Measure C(Time,X)).map (fun γ => γ 0))
        ((ρs j : Measure C(Time,X)).map (fun γ => γ 1))
        ((ρs j : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))) ∧
      Tendsto ρs atTop (𝓝 ρ) ∧
      ∀ f : C(Time,X) → ℝ, Integrable f (ρ : Measure C(Time,X)) →
        Tendsto (fun j => ∫γ,f γ ∂(ρs j : Measure C(Time,X)))
          atTop (𝓝 (∫γ,f γ ∂(ρ : Measure C(Time,X)))) := by
  obtain ⟨ρs,R,w,he,hw,hb,hl,hle,hR,hlim,hint⟩ :=
    weighted_probability_recovery ρ (ContinuousMap.const Time p)
  refine ⟨ρs,fun j => max (R j) 0,fun _ => le_max_right _ _,hle,?_,?_,?_,hlim,hint⟩
  · intro j
    exact (hg.filter_mono Measure.smul_absolutelyContinuous.ae_le).filter_mono
      (hle j).absolutelyContinuous.ae_le
  · intro j
    filter_upwards [hR j] with γ hγ
    intro t
    have hd := ContinuousMap.dist_apply_le_dist (f:=ContinuousMap.const Time p) (g:=γ) t
    have ht : dist (γ t) p≤R j := by
      simpa only [ContinuousMap.const_apply,dist_comm p (γ t)] using hd.trans hγ
    exact ht.trans (le_max_left _ _)
  · intro j
    exact dominated_optimal_plan (ρ : Measure C(Time,X)) (ρs j : Measure C(Time,X)) hp hc (hle j)

end RegularPointCoordinates

end

end OAI
