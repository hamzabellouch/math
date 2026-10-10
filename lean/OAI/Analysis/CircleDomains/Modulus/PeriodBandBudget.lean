import OAI.Analysis.CircleDomains.Selection.PeriodBandGraph
import OAI.Analysis.CircleDomains.Topology.FreeBandNeighborhoods
import OAI.Analysis.CircleDomains.Rigidity.TraceBandLevel
import OAI.Analysis.CircleDomains.Topology.SphereLevels

namespace OAI

/-! Period levels have the dust-incidence budget, including budget one
at the singular point. Zero local band width gives the unique free trace
used by independent-level selection. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem periodBandGraph_incidence_le_budget {ι : Type*}
    (D M : Set Sphere) (hdense : Dense D) (b : Sphere)
    (V : ι → Set Sphere) (hmiss : ∀ i, b ∉ V i) (hcover : M \ {b} ⊆ ⋃ i, V i)
    (f : ι → Sphere → ℝ) (bound : ι → ℝ)
    (hbound : ∀ i x, x ∈ D → |f i x| ≤ bound i)
    (hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j))
    (m : Sphere → ℝ≥0∞) (hb : 1 ≤ m b)
    (hband : ∀ i x, x ∈ M ∩ V i → ENNReal.ofReal
      (limsup (f i) (𝓝[D] x) - liminf (f i) (𝓝[D] x)) ≤ m x) (x : Sphere) :
    volume {θ | (x, θ) ∈ periodBandGraph D M b V f} ≤ m x := by
  by_cases hxM : x ∈ M
  · by_cases hxb : x = b
    · subst x
      exact (measure_mono (subset_univ _)).trans (by simpa [AddCircle.measure_univ] using hb)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hxM, hxb⟩)
      rw [periodBandGraph_fiber_on_patch D M b V f hmiss hcompat hxM hi]
      exact (volume_circleBandGraph_incidence_le_budget (hbound i)
        (by rw [hdense.closure_eq]; trivial) le_rfl).trans (hband i x ⟨hxM, hi⟩)
  · have hempty : {θ | (x, θ) ∈ periodBandGraph D M b V f} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun θ hθ => hxM hθ.1
    rw [hempty, measure_empty]
    exact bot_le

theorem periodBandGraph_unique_of_zero_band {ι : Type*}
    (D M : Set Sphere) (hdense : Dense D) (b : Sphere)
    (V : ι → Set Sphere) (hmiss : ∀ i, b ∉ V i) (hcover : M \ {b} ⊆ ⋃ i, V i)
    (f : ι → Sphere → ℝ) (bound : ι → ℝ)
    (hbound : ∀ i x, x ∈ D → |f i x| ≤ bound i)
    (hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j))
    {x : Sphere} (hxb : x ≠ b)
    (hband : ∀ i, x ∈ M ∩ V i → limsup (f i) (𝓝[D] x) - liminf (f i) (𝓝[D] x) ≤ 0)
    {s t : UnitAddCircle} (hs : (x, s) ∈ periodBandGraph D M b V f)
    (ht : (x, t) ∈ periodBandGraph D M b V f) : s = t := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hs.1, hxb⟩)
  have hxcl : x ∈ closure D := by rw [hdense.closure_eq]; trivial
  have htrace := real_band_fiber_eq_trace_of_zero_width (hbound i) hxcl (hband i ⟨hs.1, hi⟩)
  have hs' := (periodBandGraph_on_patch D M b V f hmiss hcompat hi s).mp hs
  have ht' := (periodBandGraph_on_patch D M b V f hmiss hcompat hi t).mp ht
  have heq (θ : UnitAddCircle) (hθ : (x, θ) ∈ circleBandGraph D (f i)) :
      (realBoundaryTrace D (f i) x : UnitAddCircle) = θ := by
    obtain ⟨⟨y, r⟩, hr, he⟩ := hθ
    have hy : y = x := congrArg Prod.fst he
    subst y
    have hrEq := (htrace r).mp hr
    simpa only [hrEq] using congrArg Prod.snd he
  exact (heq s hs'.2).symm.trans (heq t ht'.2)

end CircleDomainRigidity

end OAI
