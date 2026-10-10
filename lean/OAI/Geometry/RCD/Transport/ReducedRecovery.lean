import OAI.Geometry.RCD.Transport.BoundedEndpointNode
import OAI.Geometry.RCD.Transport.RecoveryPlanCost
import OAI.Geometry.RCD.Transport.SelectedPlanLengthWindows

namespace OAI

/-! # Actual compressed reduced-CD recovery of an unbounded optimal plan

The fixed endpoint capacity controls each fixed length window independently
of the radii of the bounded recovery. The full transport costs converge.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.reduced_recovery_sequence
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (ρ : ProbabilityMeasure C(Time,X)) (p : X)
    (hg : ∀ᵐ γ ∂(ρ : Measure C(Time,X)), IsGeodesic γ)
    (hp : IsOptimalCoupling ((ρ : Measure C(Time,X)).map (fun γ => γ 0))
      ((ρ : Measure C(Time,X)).map (fun γ => γ 1))
      ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))))
    (hcost : transportCost ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))≠∞)
    {C : ℝ≥0∞} (hC : C≠∞)
    (hc : ∀ t : Time, t=0 ∨ t=1 → (ρ : Measure C(Time,X)).map (fun γ => γ t)≤C • hausdorff n X) :
    ∃ πs : ℕ → ProbabilityMeasure C(Time,X),
      (∀ j, ∀ᵐ γ ∂(πs j : Measure C(Time,X)), IsGeodesic γ) ∧
      (∀ t : Time, t=0 ∨ t=1 → ∀ j, (πs j : Measure C(Time,X)).map (fun γ => γ t)≤
        (2 : ℝ≥0∞) • (ρ : Measure C(Time,X)).map (fun γ => γ t)) ∧
      (∀ t : Time, t=0 ∨ t=1 → Tendsto (fun j => (πs j).map (fun γ => γ t))
        atTop (𝓝 (ρ.map (fun γ => γ t)))) ∧
      Tendsto (fun j => transportCost ((πs j : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))))
        atTop (𝓝 (transportCost ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))))) ∧
      (∀ j D, 0≤D → ∀ t : Time,
        (((πs j : Measure C(Time,X)).restrict {γ | dist (γ 0) (γ 1)<D}).map (fun γ => γ t))≤
          compressionBudget K n D ((2 : ℝ≥0∞)*C) • hausdorff n X) ∧
      ∀ j t, ReducedRenyiChordBound (hausdorff n X) K N (πs j : Measure C(Time,X)) t := by
  let : SeparableSpace X := hX.separable
  obtain ⟨ρs,R,hR,hle,hgs,hs,hps,hlim,hint⟩ := bounded_optimal_recovery ρ p hg hp hcost
  have h2C : (2 : ℝ≥0∞)*C≠∞ := ENNReal.mul_ne_top (by norm_num) hC
  let a (j : ℕ) := boundedEndpointNode n (ρs j) p (hR j) (hs j) h2C
    (bounded_recovery_endpoint_bound n _ _ (hle j) 0 (hc 0 (Or.inl rfl)))
    (bounded_recovery_endpoint_bound n _ _ (hle j) 1 (hc 1 (Or.inr rfl)))
  have hx (j : ℕ) := hX.exists_reduced_plan_with_length_windows K n hn hK hN (a j)
  choose πs hπg hπp hπcd hπw using hx
  have he (j : ℕ) (t : Time) (ht : t=0 ∨ t=1) :
      (πs j : Measure C(Time,X)).map (fun γ => γ t)=
        (ρs j : Measure C(Time,X)).map (fun γ => γ t) := by
    have hh := optimalPlan_endpoints (a j).left (a j).right _ (hπp j)
    rcases ht with rfl | rfl
    · exact hh.1
    · exact hh.2
  have heP (j : ℕ) (t : Time) (ht : t=0 ∨ t=1) :
      (πs j).map (fun γ => γ t)=(ρs j).map (fun γ => γ t) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact he j t ht
  refine ⟨πs,hπg,?_,?_,?_,hπw,hπcd⟩
  · intro t ht j
    rw [he j t ht,←Measure.map_smul _ (measurable_path_eval t).aemeasurable]
    exact Measure.map_mono (hle j) (measurable_path_eval t)
  · intro t ht
    simp_rw [heP _ t ht]
    exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim (continuous_eval_const t)
  · have hec (j : ℕ) :
        transportCost ((πs j : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))=
          transportCost ((ρs j : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))) := by
      exact le_antisymm ((hπp j).2.2 _ (hps j).1 (hps j).2.1)
        ((hps j).2.2 _ (hπp j).1 (hπp j).2.1)
    simp_rw [hec]
    exact recovery_cost_tendsto ρs ρ hle hcost
      (hint _ (path_cost_integrable (ρ : Measure C(Time,X)) hcost))

end RegularPointCoordinates

end

end OAI
