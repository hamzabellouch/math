import OAI.Geometry.RCD.Transport.ComponentScalarChord
import OAI.Geometry.RCD.Transport.LengthComponentIntegral

namespace OAI

/-! # Interpolation summed over a finite partition of lengths -/

open Set Filter MeasureTheory Metric TopologicalSpace Function
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.finite_component_scalar_chord
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    {m : ℕ} (hm : RenyiDyadicMaximal (hausdorff n X) (1-1/N) (fun t => π.map (fun γ => γ t)) m)
    {ι : Type*} (S : ι → Set ℝ) (s : Finset ι) (hS : ∀ i, MeasurableSet (S i))
    (hd : (s : Set ι).Pairwise (Disjoint on S))
    (hcover : ∀ᵐ γ ∂π, ∃ i∈s, dist (γ 0) (γ 1)∈S i)
    (D : ι → ℝ) (hD0 : ∀ i∈s, 0≤D i) (hD : ∀ i∈s, ∀ d∈S i, d≤D i)
    {t : Time} (ht : t∈dyadicGrid m) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
    (∑ i∈s, reducedChord K (N+1) (D i)
      (renyiIntegral (hausdorff n X) ((π.restrict {γ | dist (γ 0) (γ 1)∈S i}).map (fun γ => γ 0)) N)
      (renyiIntegral (hausdorff n X) ((π.restrict {γ | dist (γ 0) (γ 1)∈S i}).map (fun γ => γ 1)) N) t) ≤
      renyiIntegral (hausdorff n X) (π.map (fun γ => γ t)) N := by
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let κ := fun i => π.restrict {γ | dist (γ 0) (γ 1)∈S i}
  have hN1 : 1<N := by
    have hnR : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  have hz : renyiIntegral μ 0 N=0 := by
    have hh := renyiIntegral_finset_additive μ (fun _ : Unit => (0 : Measure X)) ∅ (by simp) hN1
    simpa only [Finset.sum_empty] using hh
  have hb (i) (hi : i∈s) : reducedChord K (N+1) (D i)
      (renyiIntegral μ ((κ i).map (fun γ => γ 0)) N)
      (renyiIntegral μ ((κ i).map (fun γ => γ 1)) N) t≤
        renyiIntegral μ ((κ i).map (fun γ => γ t)) N := by
    by_cases hi0 : κ i univ=0
    · have he : κ i=0 := Measure.measure_univ_eq_zero.mp hi0
      simp only [he,Measure.map_zero,hz,reducedChord,mul_zero,add_zero,le_refl]
    · exact hX.component_scalar_chord K n hn hK hN a π hg hp hC hc hm (hS i)
        (κ i) rfl hi0 (hD0 i hi)
        ((ae_restrict_mem ((hS i).preimage ((measurable_path_eval 0).dist (measurable_path_eval 1)))).mono
          (fun γ hγ => hD i hi _ hγ)) t ht
  exact (Finset.sum_le_sum hb).trans_eq
    (hX.length_partition_renyiIntegral K n hn a π hg hp S s hS hd hcover hN1 ht0 ht1)

end RegularPointCoordinates

end

end OAI
