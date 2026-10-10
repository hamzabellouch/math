import OAI.Analysis.CircleDomains.Rigidity.RawArcNullTrace
import OAI.Analysis.CircleDomains.Topology.LevelQuotient
import OAI.Analysis.CircleDomains.Selection.LusinInput

namespace OAI

/-! The raw barrier has Haar-null free trace on the nondegenerate components
of an actual compact quotient level union. The topology comes from finite
physical length. Arc existence uses only the connected-open specialization
of Lorimer (1981), recorded in `ArcNullImage`. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem raw_barrier_null_component_traces
    {X Y : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H B F : Set X} (hH : IsCompact H) (hB : IsCompact B)
    (hTD : IsTotallyDisconnected B)
    (hbad : π '' d.physicalDomainᶜ ⊆ B)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hUB : Disjoint d.quotientDomain B)
    (hF : MeasurableSet F) (hFB : F ⊆ B)
    (harcs : ∀C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ d.physicalDomain) < ∞)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hg : (∫⁻y in d.physicalDomain ∩ π ⁻¹' H, g y ∂(μH[1] : Measure Y)) < ∞)
    (hm : atomicBoundaryMeasure m H < ∞) (hmF : ∀x ∈ F, m x = 0)
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u v : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (htrace : ∀x ∈ F, Tendsto u (𝓝[d.quotientDomain] x) (𝓝 (v x)))
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels)
    (hlevel : ∀x ∈ H, ∃i, (levels i, x) ∈ d.levels (labels i)) :
    HasFiniteLargeContinuumBound H ∧
      ∀ C : Set H, (∃x, C = connectedComponent x) → C.Nontrivial →
        volume ((fun x : H => (v x.val : UnitAddCircle)) ''
          ((Subtype.val ⁻¹' F) ∩ C)) = 0 := by
  obtain ⟨hbound, _, hloc⟩ := level_topology_of_finite_physical_length
    π hπ hsurj hfiber hG hB hTD hbad hH hlength
  refine ⟨hbound, ?_⟩
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  rintro C ⟨x, rfl⟩ _
  let C := connectedComponent x
  have hC : IsCompact C := isClosed_connectedComponent.isCompact
  let : LocallyConnectedSpace C := hloc C hC isConnected_connectedComponent
  let A : Set X := Subtype.val '' C
  have hA : IsCompact A := hC.image continuous_subtype_val
  have hAH : A ⊆ H := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  let e : C ≃ₜ A := Topology.IsEmbedding.subtypeVal.homeomorphImage C
  let : LocallyConnectedSpace A := e.symm.isOpenEmbedding.locallyConnectedSpace
  have hn := raw_barrier_null_trace_on_continuum d hU hdisj π hπ.measurable he
    hH.isClosed.measurableSet hTD hBU hUB hF hFB hA hAH (harcs A hA inferInstance)
    hlength g m hg hm hmF ν N u v hpay htrace n labels levels hN hlevel
  have himage : (fun z : H => (v z.val : UnitAddCircle)) ''
      ((Subtype.val ⁻¹' F) ∩ C) =
      ((↑) : ℝ → UnitAddCircle) '' (v '' (F ∩ A)) := by
    ext t
    constructor
    · rintro ⟨z, ⟨hzF, hzC⟩, rfl⟩
      exact ⟨v z.val, ⟨z.val, ⟨hzF, z, hzC, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨z, ⟨hzF, y, hyC, rfl⟩, rfl⟩, rfl⟩
      exact ⟨y, ⟨hzF, hyC⟩, rfl⟩
  rw [himage]
  exact volume_addCircle_image_eq_zero hn

end CircleDomainRigidity

end

end OAI
