import OAI.Geometry.RCD.Transport.PairedPrefixUniqueness
import Mathlib.Topology.Order.DenselyOrdered

namespace OAI

/-! # One common null set gives uniqueness of entire paired paths -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem paired_common_prefix_unique (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ]
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π)
    (T : Time) (hT : 0 < T) (hpast : ∀ᵐ z ∂σ, z ∈ pathAgreement (T:ℝ)) :
    ∀ᵐ z ∂σ, z.1=z.2 := by
  obtain ⟨D,hD,hdense,_,hnotop⟩ := exists_countable_dense_no_bot_top Time
  let : Countable D := hD.to_subtype
  have hq (q : D) : (q:Time) < 1 := by
    by_contra h
    have he : (q:Time)=1 := le_antisymm q.val.property.2 (le_of_not_gt h)
    have hn := hnotop 1 (fun a => a.property.2)
    exact hn (he ▸ q.property)
  have ha : ∀ q : D, ∀ᵐ z ∂σ, z.1 (q:Time)=z.2 (q:Time) :=
    fun q => hX.paired_common_prefix_point hn p hR π hg hp hC hc hs₀ hs₁ σ hl hr T q hT (hq q) hpast
  filter_upwards [ae_all_iff.mpr ha] with z hz
  apply ContinuousMap.ext
  have hclosed : IsClosed {q : Time | z.1 q=z.2 q} :=
    isClosed_eq z.1.continuous z.2.continuous
  have hsub : D ⊆ {q : Time | z.1 q=z.2 q} := fun q hq => hz ⟨q,hq⟩
  have hall := closure_minimal hsub hclosed
  rw [hdense.closure_eq] at hall
  exact fun q => hall (mem_univ q)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
