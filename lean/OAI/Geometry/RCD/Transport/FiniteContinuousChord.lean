import OAI.Geometry.RCD.Transport.FiniteComponentChord
import OAI.Geometry.RCD.Transport.RenyiPathSemicontinuity

namespace OAI

/-! # Finite length-partition bounds at all times

The weighted scalar sum is continuous. Upper semicontinuity of the actual
Rényi entropy extends its dyadic lower bound to the whole interval.
-/

open Set Filter MeasureTheory Metric TopologicalSpace Function
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.finite_component_chord_all_times
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (hm : ∀ m, RenyiDyadicMaximal (hausdorff n X) (1-1/N) (fun t => π.map (fun γ => γ t)) m)
    {ι : Type*} (S : ι → Set ℝ) (s : Finset ι) (hS : ∀ i, MeasurableSet (S i))
    (hd : (s : Set ι).Pairwise (Disjoint on S))
    (hcover : ∀ᵐ γ ∂π, ∃ i∈s, dist (γ 0) (γ 1)∈S i)
    (D : ι → ℝ) (hD0 : ∀ i∈s, 0≤D i) (hD : ∀ i∈s, ∀ d∈S i, d≤D i) :
    ∀ t : Time, (∑ i∈s, reducedChord K (N+1) (D i)
      (renyiIntegral (hausdorff n X) ((π.restrict {γ | dist (γ 0) (γ 1)∈S i}).map (fun γ => γ 0)) N)
      (renyiIntegral (hausdorff n X) ((π.restrict {γ | dist (γ 0) (γ 1)∈S i}).map (fun γ => γ 1)) N) t) ≤
      renyiIntegral (hausdorff n X) (π.map (fun γ => γ t)) N := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let := a.left_probability
  let := a.right_probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let B := closedBall a.center (3*a.radius)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hN1 : 1<N := by
    have hnR : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x∈B := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right π hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono (fun γ hγ => hγ.2 t)
  let κ := fun i => π.restrict {γ | dist (γ 0) (γ 1)∈S i}
  have hsκ (i) (t : Time) : ∀ᵐ x ∂(κ i).map (fun γ => γ t), x∈B :=
    (hs t).filter_mono (Measure.map_mono Measure.restrict_le_self (measurable_path_eval t)).absolutelyContinuous.ae_le
  have hfκ (i) (t : Time) : renyiIntegral μ ((κ i).map (fun γ => γ t)) N≠∞ :=
    renyiIntegral_ne_top_of_support μ _ measurableSet_closedBall (hsκ i t) hN1
  have hG : Continuous (fun t => ∑ i∈s, reducedChord K (N+1) (D i)
      (renyiIntegral μ ((κ i).map (fun γ => γ 0)) N)
      (renyiIntegral μ ((κ i).map (fun γ => γ 1)) N) t) :=
    continuous_finsetSum s (fun i hi => continuous_reducedChord hK (by linarith)
      (hD0 i hi) (hfκ i 0) (hfκ i 1))
  let v : ProbabilityMeasure C(Time,X) := ⟨π,inferInstance⟩
  have hu := upperSemicontinuous_supported_renyiPath μ measurableSet_closedBall
    (fun t => v.map (fun γ => γ t)) (continuous_time_marginals v) hs hN1
  have hdense : Dense ((⋃ m, dyadicGrid m) ∩ Ioo (0:Time) 1) := by
    apply dense_dyadicGrid.inter_of_isOpen_right _ isOpen_Ioo
    have h01 : (0:Time)≠1 := by
      intro hh
      have hh' := congrArg (fun t : Time => (t:ℝ)) hh
      norm_num at hh'
    rw [dense_iff_closure_eq,closure_Ioo h01]
    exact Set.eq_univ_of_forall (fun t => ⟨t.property.1,t.property.2⟩)
  apply ge_continuous_of_dense hu hG hdense
  intro t ht
  obtain ⟨m,htm⟩ := mem_iUnion.mp ht.1
  exact hX.finite_component_scalar_chord K n hn hK hN a π hg hp hC hc (hm m)
    S s hS hd hcover D hD0 hD htm ht.2.1 ht.2.2

end RegularPointCoordinates

end

end OAI
