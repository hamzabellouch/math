import OAI.Geometry.RCD.Transport.ComponentScalarMidpoint

namespace OAI

/-! # Exact Rényi sums for finite length partitions

Disjoint length bins give disjoint spatial components at every interior
time. No such assertion is made at the two endpoints.
-/

open Set Filter MeasureTheory Metric TopologicalSpace Function
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem sum_length_restrictions [SeparableSpace X] {ι : Type*}
    (π : Measure C(Time,X)) (S : ι → Set ℝ) (s : Finset ι)
    (hS : ∀ i, MeasurableSet (S i))
    (hd : (s : Set ι).Pairwise (Disjoint on S))
    (hcover : ∀ᵐ γ ∂π, ∃ i∈s, dist (γ 0) (γ 1)∈S i) :
    (∑ i∈s, π.restrict {γ | dist (γ 0) (γ 1)∈S i})=π := by
  classical
  let A := fun i => {γ : C(Time,X) | dist (γ 0) (γ 1)∈S i}
  have hA (i) : MeasurableSet (A i) :=
    (hS i).preimage ((measurable_path_eval 0).dist (measurable_path_eval 1))
  have hAd : (s : Set ι).Pairwise (Disjoint on A) := by
    intro i hi j hj hij
    exact (hd hi hj hij).preimage _
  have hae : ∀ᵐ γ ∂π, γ∈⋃ i∈s, A i := by
    simpa only [mem_iUnion,exists_prop,A,mem_ofPred_eq] using hcover
  change (∑ i∈s, π.restrict (A i))=π
  rw [←Measure.sum_coe_finset,←Measure.restrict_biUnion_finset hAd hA]
  exact Measure.restrict_eq_self_of_ae_mem hae

theorem NoncollapsedRCD.length_partition_renyiIntegral
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {ι : Type*} (S : ι → Set ℝ) (s : Finset ι) (hS : ∀ i, MeasurableSet (S i))
    (hd : (s : Set ι).Pairwise (Disjoint on S))
    (hcover : ∀ᵐ γ ∂π, ∃ i∈s, dist (γ 0) (γ 1)∈S i)
    {N : ℝ} (hN : 1<N) {t : Time} (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
    (∑ i∈s, renyiIntegral (hausdorff n X)
      ((π.restrict {γ | dist (γ 0) (γ 1)∈S i}).map (fun γ => γ t)) N)=
      renyiIntegral (hausdorff n X) (π.map (fun γ => γ t)) N := by
  let : SeparableSpace X := hX.separable
  let : IsProbabilityMeasure a.left := a.left_probability
  let : IsProbabilityMeasure a.right := a.right_probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let κ := fun i => π.restrict {γ | dist (γ 0) (γ 1)∈S i}
  have hA (i) : MeasurableSet {γ : C(Time,X) | dist (γ 0) (γ 1)∈S i} :=
    (hS i).preimage ((measurable_path_eval 0).dist (measurable_path_eval 1))
  have hsep : ∀ i∈s, ∀ j∈s, i≠j → (κ i).map (fun γ => γ t) ⟂ₘ (κ j).map (fun γ => γ t) := by
    intro i hi j hj hij
    have hκi : ∀ᵐ γ ∂κ i, dist (γ 0) (γ 1)∈S i := ae_restrict_mem (hA i)
    have hκj : ∀ᵐ γ ∂κ j, dist (γ 0) (γ 1)∉S i :=
      (ae_restrict_mem (hA j)).mono (fun γ hγ hx => Set.disjoint_left.mp (hd hi hj hij) hx hγ)
    exact hX.optimal_components_mutuallySingular K n hn a.left a.right
      (Measure.absolutelyContinuous_of_le_smul a.left_bound) a.center a.radius_nonneg
      a.left_support a.right_support π π hg hg hp hp (κ i) (κ j)
      Measure.restrict_le_self Measure.restrict_le_self ht0 ht1 (hS i) hκi hκj
  have he := renyiIntegral_finset_additive μ (fun i => (κ i).map (fun γ => γ t)) s hsep hN
  rw [←he,←Measure.map_finset_sum (measurable_path_eval t).aemeasurable]
  congr 2
  exact sum_length_restrictions π S s hS hd hcover

end RegularPointCoordinates

end

end OAI
