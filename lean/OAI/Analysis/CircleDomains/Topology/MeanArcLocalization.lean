import OAI.Analysis.CircleDomains.Topology.SimpleArcPhysicalLocalization

namespace OAI

/-! Localized occupation comparison after measurable simple-arc selection. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {G : Set Y} {U : Set X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma physicalOccupationCode_localized_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ α : C(PathTime, X)) (hγ : physicalDomainLength e y₀ γ < ∞)
    (hi : Injective α) (hs : range α ⊆ range γ)
    {W : Set Y} (hW : MeasurableSet W) (y : Y)
    (hout : ∀ t, α t ∈ U → physicalValue e y₀ (α t) ∉ W → physicalValue e y₀ (α t) = y) :
    physicalOccupationCode e y₀ α ≤ (physicalOccupationCode e y₀ γ).restrict W := by
  have hα : physicalDomainLength e y₀ α < ∞ :=
    (simple_subarc_physical_length_le e hU y₀ ⟨γ, hγ⟩ α hi hs).trans_lt hγ
  rw [physicalOccupationCode_eq e y₀ ⟨α, hα⟩, physicalOccupationCode_eq e y₀ ⟨γ, hγ⟩]
  exact simple_subarc_physical_localized_le e hU y₀ ⟨γ, hγ⟩ ⟨α, hα⟩ hi hs hW y hout

omit [BorelSpace X] in
lemma physicalOccupationCode_collar_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπm : Measurable π) (hπ : ∀ y : G, π y.val = (e y).val)
    (γ α : C(PathTime, X)) (hγ : physicalDomainLength e y₀ γ < ∞)
    (hi : Injective α) (hs : range α ⊆ range γ)
    (V : Set X) (hV : MeasurableSet V) (hout : ∀ t, α t ∉ V → α t = α ⊥) :
    physicalOccupationCode e y₀ α ≤ (physicalOccupationCode e y₀ γ).restrict (π ⁻¹' V) := by
  apply physicalOccupationCode_localized_le e hU y₀ γ α hγ hi hs (hπm hV)
    (physicalValue e y₀ (α ⊥))
  intro t ht hn
  apply congrArg (physicalValue e y₀)
  apply hout t
  simpa only [mem_preimage, physicalValue_projects e y₀ π hπ ht] using hn

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [BorelSpace X] in
lemma meanPhysicalOccupation_map_collar_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπm : Measurable π) (hπ : ∀ y : G, π y.val = (e y).val)
    (μ : ProbabilityMeasure C(PathTime, X)) (f : C(PathTime, X) → C(PathTime, X))
    (hfm : AEMeasurable f (μ : Measure C(PathTime, X)))
    (V : Set X) (hV : MeasurableSet V)
    (hgood : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)),
      physicalDomainLength e y₀ γ < ∞ ∧ Injective (f γ) ∧ range (f γ) ⊆ range γ ∧
      ∀ t, (f γ) t ∉ V → (f γ) t = (f γ) ⊥) :
    meanPhysicalOccupation e y₀ (μ.map f) ≤ (meanPhysicalOccupation e y₀ μ).restrict (π ⁻¹' V) := by
  apply Measure.le_iff.mpr
  intro S hS
  have hm : Measurable (fun γ => physicalOccupationCode e y₀ γ S) :=
    (Measure.measurable_coe hS).comp (measurable_physicalOccupationCode e hU y₀)
  rw [meanPhysicalOccupation_apply e hU y₀ _ hS, ProbabilityMeasure.toMeasure_map,
    lintegral_map' hm.aemeasurable hfm, Measure.restrict_apply hS,
    meanPhysicalOccupation_apply e hU y₀ _ (hS.inter (hπm hV))]
  apply lintegral_mono_ae
  filter_upwards [hgood] with γ hγ
  have h := physicalOccupationCode_collar_le e hU y₀ π hπm hπ γ (f γ)
    hγ.1 hγ.2.1 hγ.2.2.1 V hV hγ.2.2.2 S
  rwa [Measure.restrict_apply hS] at h

end CircleDomainRigidity

end

end OAI
