import OAI.Analysis.CircleDomains.Modulus.RawArcPayment
import OAI.Analysis.CircleDomains.Probability.ArcNullImage

namespace OAI

/-! The actual raw barrier has a null free trace on every locally connected
compact subcontinuum of a good prior level union. The only arc-existence
input is the published connected-open specialization recorded in ArcNullImage. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem raw_barrier_null_trace_on_continuum
    {X Y : Type*} [MetricSpace X] [SecondCountableTopology X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H B F C : Set X} (hH : MeasurableSet H) (hB : IsTotallyDisconnected B)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hUB : Disjoint d.quotientDomain B)
    (hF : MeasurableSet F) (hFB : F ⊆ B) (hC : IsCompact C) (hCH : C ⊆ H)
    [LocallyConnectedSpace C] (harcs : HasSimpleArcsInConnectedOpens C)
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
    volume (v '' (F ∩ C)) = 0 := by
  let μ := levelPaymentMeasure π d.physicalDomain H g m
  let : IsFiniteMeasure μ := levelPaymentMeasure_finite π hπ d.physicalDomain H g m hg hm
  have hπG : MapsTo π d.physicalDomain d.quotientDomain := by
    intro y hy
    rw [he ⟨y, hy⟩]
    exact (d.domainEquiv ⟨y, hy⟩).property
  have hμF : μ F = 0 := levelPaymentMeasure_free_null π hπ hF hπG hUB hFB g m hmF
  let μC : Measure C := μ.comap Subtype.val
  have hemb : MeasurableEmbedding (Subtype.val : C → X) :=
    MeasurableEmbedding.subtype_coe hC.isClosed.measurableSet
  let : IsFiniteMeasure μC := ⟨by
    change μ.comap Subtype.val univ < ∞
    rw [hemb.comap_apply]
    exact measure_lt_top μ _⟩
  have hμCF : μC (Subtype.val ⁻¹' F) = 0 := by
    rw [show μC (Subtype.val ⁻¹' F) = μ (Subtype.val '' (Subtype.val ⁻¹' F)) from
      hemb.comap_apply μ _]
    exact measure_mono_null (image_preimage_subset _ _) hμF
  have hn : volume ((fun x : C => v x.val) '' (Subtype.val ⁻¹' F)) = 0 := by
    suffices h : volume ((fun x : C => v x.val) '' ((Subtype.val ⁻¹' F) ∩ univ)) = 0 by
      simpa only [inter_univ] using h
    apply null_image_of_simple_arc_payment (μ := μC) harcs isOpen_univ
      (by simpa only [inter_univ] using hμCF) (fun x : C => v x.val) (by norm_num : (0 : ℝ) ≤ 4)
    intro x hx y hy γ hγ _
    let δ : Path x.val y.val := γ.map continuous_subtype_val
    have hδ : Injective δ := Subtype.val_injective.comp hγ
    have hδH : range δ ⊆ H := by
      rintro z ⟨t, rfl⟩
      exact hCH (γ t).property
    have hp := raw_simple_arc_trace_payment d hU hdisj π hπ he hH hB hBU hlength
      g m inferInstance ν N u hpay δ hδ hδH n labels levels hN
      (fun t => hlevel _ (hCH (γ t).property)) (htrace x.val hx.1) (htrace y.val hy.1)
    have hmass : μC.real (range γ) = μ.real (range δ) := by
      rw [measureReal_def, measureReal_def, hemb.comap_apply]
      congr 1
      apply congrArg μ
      change Subtype.val '' range γ = range (Subtype.val ∘ γ)
      exact (range_comp _ _).symm
    rwa [hmass]
  have himage : (fun x : C => v x.val) '' (Subtype.val ⁻¹' F) = v '' (F ∩ C) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, ⟨hx, x.property⟩, rfl⟩
    · rintro ⟨x, ⟨hxF, hxC⟩, rfl⟩
      exact ⟨⟨x, hxC⟩, hxF, rfl⟩
  rwa [himage] at hn

end CircleDomainRigidity

end

end OAI
