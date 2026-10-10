import OAI.Geometry.RCD.Transport.ReducedRecovery
import OAI.Geometry.RCD.Transport.DominatedEndpointTails
import OAI.Geometry.RCD.Transport.WeakOptimalRecovery

namespace OAI

/-! # The actual noncompact recovery limit

The bounded reduced-CD plans converge to an optimal geodesic plan. Every
bounded length window keeps its uniform compression constant. This does
not yet assert passage of the reduced entropy inequality to the limit.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.reduced_recovery_limit
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (ρ : ProbabilityMeasure C(Time,X)) (p : X)
    (hg : ∀ᵐ γ ∂(ρ : Measure C(Time,X)), IsGeodesic γ)
    (hp : IsOptimalCoupling ((ρ : Measure C(Time,X)).map (fun γ => γ 0))
      ((ρ : Measure C(Time,X)).map (fun γ => γ 1))
      ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))))
    (hcost : transportCost ((ρ : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))≠∞)
    {C : ℝ≥0∞} (hC : C≠∞)
    (hc : ∀ t : Time, t=0 ∨ t=1 → (ρ : Measure C(Time,X)).map (fun γ => γ t)≤C • hausdorff n X) :
    ∃ (π : ProbabilityMeasure C(Time,X)) (πs : ℕ → ProbabilityMeasure C(Time,X)),
      Tendsto πs atTop (𝓝 π) ∧
      (∀ j t, ReducedRenyiChordBound (hausdorff n X) K N (πs j : Measure C(Time,X)) t) ∧
      (∀ᵐ γ ∂(π : Measure C(Time,X)), IsGeodesic γ) ∧
      IsOptimalCoupling ((ρ : Measure C(Time,X)).map (fun γ => γ 0))
        ((ρ : Measure C(Time,X)).map (fun γ => γ 1))
        ((π : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))) ∧
      (∀ D : ℝ, 0≤D → ∀ t : Time,
        (((π : Measure C(Time,X)).restrict {γ | dist (γ 0) (γ 1)<D}).map (fun γ => γ t))≤
          compressionBudget K n D ((2 : ℝ≥0∞)*C) • hausdorff n X) ∧
      ∀ t : Time, (π : Measure C(Time,X)).map (fun γ => γ t) ≪ hausdorff n X := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨πs,hgs,hdom,he,hcs,hw,hcd⟩ := hX.reduced_recovery_sequence K n hn hK hN ρ p hg hp hcost hC hc
  have ht := dominated_endpoint_tails πs (ρ.map (fun γ => γ 0)) (ρ.map (fun γ => γ 1)) p
    (hdom 0 (Or.inl rfl)) (hdom 1 (Or.inr rfl))
  obtain ⟨π,φ,hφ,hlim⟩ := geodesic_plans_subsequence_of_endpoint_tails πs p hgs ht
  have hcomp (D : ℝ) (hD : 0≤D) (t : Time) :
      (((π : Measure C(Time,X)).restrict {γ | dist (γ 0) (γ 1)<D}).map (fun γ => γ t))≤
        compressionBudget K n D ((2 : ℝ≥0∞)*C) • μ := by
    apply weak_length_window_compression μ (πs ∘ φ) π hlim t D
      (compressionBudget_ne_top K n D (ENNReal.mul_ne_top (by norm_num) hC))
    exact fun j => hw (φ j) D hD t
  refine ⟨π,πs ∘ φ,hlim,fun j t => hcd (φ j) t,
    weak_limit_geodesic _ π hlim (fun j => hgs (φ j)),?_,hcomp,?_⟩
  · exact weak_optimal_of_recovery _ π ρ hlim
      ((he 0 (Or.inl rfl)).comp hφ.tendsto_atTop)
      ((he 1 (Or.inr rfl)).comp hφ.tendsto_atTop)
      (hcs.comp hφ.tendsto_atTop) hp
  · intro t
    apply absolutelyContinuous_of_length_windows μ (π : Measure C(Time,X)) t
    intro j
    exact Measure.absolutelyContinuous_of_le_smul (hcomp ((j:ℝ)+1) (by positivity) t)

end RegularPointCoordinates

end

end OAI
