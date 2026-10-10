import OAI.Geometry.RCD.Transport.PairedInitialUniqueness
import OAI.Geometry.RCD.Heat.ConditionalPairInverse

namespace OAI

/-! # Measurable inversion of initial evaluation for the actual compressed plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem compressed_initial_inverse (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    :
    ∃ g : X → C(Time,X), Measurable g ∧ ∀ᵐ γ ∂π, g (γ 0)=γ := by
  let : CompleteSpace X := hX.complete
  let : Nonempty C(Time,X) := nonempty_of_isProbabilityMeasure π
  let σ := conditionalSelfPair π (fun γ => γ 0) (measurable_path_eval 0)
  obtain ⟨hσ₀,hσ₁⟩ := conditionalSelfPair_marginals π (fun γ => γ 0) (measurable_path_eval 0)
  let : IsProbabilityMeasure σ := ⟨by
    have h := congrArg (fun m : Measure C(Time,X) => m univ) hσ₀
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using h⟩
  have hmeet : ∀ᵐ z ∂σ, z.1 0=z.2 0 :=
    conditionalSelfPair_common π (fun γ => γ 0) (measurable_path_eval 0)
  have hdiag := hX.paired_common_initial_unique hn p hR π hg hp hC hc hs₀ hs₁
    σ hσ₀.le hσ₁.le hmeet
  exact measurable_inverse_of_conditional_diagonal π (fun γ => γ 0) (measurable_path_eval 0) hdiag

theorem compressed_initial_injective (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    :
    ∃ S : Set C(Time,X), MeasurableSet S ∧ (∀ᵐ γ ∂π, γ ∈ S) ∧ InjOn (fun γ => γ 0) S := by
  obtain ⟨g,hg,hgπ⟩ := hX.compressed_initial_inverse hn p hR π hg hp hC hc hs₀ hs₁
  refine ⟨{γ | g (γ 0)=γ},measurableSet_eq_fun (hg.comp (measurable_path_eval 0)) measurable_id,hgπ,?_⟩
  intro γ hγ ζ hζ he
  exact hγ.symm.trans ((congrArg g he).trans hζ)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
