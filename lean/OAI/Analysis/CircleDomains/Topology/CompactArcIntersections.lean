import OAI.Analysis.CircleDomains.Probability.CompactPhysicalArcLaw
import OAI.Analysis.CircleDomains.Topology.SubarcIntersectionCount

namespace OAI

/-! The physical compact-arc construction simultaneously retains every
closed-set distinct-intersection estimate of the original endpoint law. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_compact_physical_arc_law_with_selection
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : G, π y.val = (e y).val)
    (μ : ProbabilityMeasure C(PathTime, Sphere)) (V : Set Sphere) (hV : IsOpen V)
    (b : Sphere)
    (hμ : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V ∧ γ ⊤ = b ∧ physicalDomainLength e y₀ γ < ∞) :
    ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere)),
      IsCompact K ∧
      (∀ α ∈ K, α ∈ terminalArcSet V b ∧ physicalDomainLength e y₀ α < ∞) ∧
      (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
      (∀ x, pathHitProbability η x ≤ 2 * pathHitProbability μ x) ∧
      (∀ x ∉ closure V, pathHitProbability η x = 0) ∧
      meanPhysicalOccupation e y₀ η ≤
        (2 : ℝ≥0∞) • (meanPhysicalOccupation e y₀ μ).restrict (π ⁻¹' V) ∧
      (∀ H : Set Sphere, IsClosed H →
        (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, Sphere))) ≤
          2 * ∫⁻ γ, pathImageCount H γ ∂(μ : Measure C(PathTime, Sphere))) ∧
      IsSubarcLawReduction μ η := by
  obtain ⟨f, hfm, hf⟩ := exists_measurable_terminal_arc_selector hselect harcs μ V hV
  have hends : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V := hμ.mono fun _ h => ⟨h.1, h.2.1⟩
  have hgood : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      physicalDomainLength e y₀ γ < ∞ ∧ Injective (f γ) ∧ range (f γ) ⊆ range γ ∧
      ∀ t, (f γ) t ∉ V → (f γ) t = (f γ) ⊥ := by
    filter_upwards [hμ] with γ hγ
    obtain ⟨hi, h0, _, hs, _, _⟩ := terminal_arc_selector_properties hV hf γ hγ.1 hγ.2.1
    refine ⟨hγ.2.2.2, hi, ?_, ?_⟩
    · exact hs.trans (image_subset_range γ _)
    · intro t ht
      exact (lastEntryTail_outside γ V (hs (mem_range_self t)) ht).trans h0.symm
  have hfinite : ∀ᵐ α : C(PathTime, Sphere) ∂(μ.map f : Measure C(PathTime, Sphere)),
      physicalDomainLength e y₀ α < ∞ := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff hfm (measurableSet_finitePhysicalDomainLength e hU y₀)).mpr
    filter_upwards [hgood] with γ hγ
    exact (simple_subarc_physical_length_le e hU y₀ ⟨γ, hγ.1⟩ (f γ) hγ.2.1 hγ.2.2.1).trans_lt hγ.1
  let S := terminalArcSet V b ∩ {α : C(PathTime, Sphere) | physicalDomainLength e y₀ α < ∞}
  have hS : MeasurableSet S := (measurableSet_terminalArcSet V hV b).inter
    (measurableSet_finitePhysicalDomainLength e hU y₀)
  have hall : ∀ᵐ α : C(PathTime, Sphere) ∂(μ.map f : Measure C(PathTime, Sphere)), α ∈ S := by
    filter_upwards [terminalArcLaw_mem μ V hV b f hfm hf
      (hμ.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩), hfinite] with α hα hfα
    exact ⟨hα, hfα⟩
  have hmass : (μ.map f : Measure C(PathTime, Sphere)) S = 1 := by
    rw [← measure_univ (μ := (μ.map f : Measure C(PathTime, Sphere)))]
    exact measure_congr (Filter.eventuallyEqSet_univ.mpr hall)
  obtain ⟨K, hKS, hK, hhalf⟩ := hS.exists_lt_isCompact
    (show (1/2 : ℝ≥0∞) < (μ.map f : Measure C(PathTime, Sphere)) S by rw [hmass]; norm_num)
  have hpos : (μ.map f : Measure C(PathTime, Sphere)) K ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1/2).trans hhalf)
  let η := restrictProbability (μ.map f) K hpos
  have hηle : (η : Measure C(PathTime, Sphere)) ≤
      (2 : ℝ≥0∞) • (μ.map f : Measure C(PathTime, Sphere)) :=
    restrictProbability_le_two (μ.map f) K hhalf.le
  refine ⟨K, η, hK, hKS, restrictProbability_ae_mem (μ.map f) K hpos hK.measurableSet, ?_, ?_, ?_, ?_,
    ⟨f, hfm, hgood.mono (fun _ h => h.2.2.1), hηle⟩⟩
  · intro x
    exact (hηle _).trans (mul_le_mul' le_rfl
      (terminalArcLaw_hit_le μ V hV f hfm hf hends x))
  · intro x hx
    apply le_antisymm ?_ bot_le
    have h := hηle {α | ∃ t : PathTime, α t = x}
    change pathHitProbability η x ≤ 2 * pathHitProbability (μ.map f) x at h
    rw [terminalArcLaw_hit_eq_zero μ V hV f hfm hf hends hx, mul_zero] at h
    exact h
  · apply (meanPhysicalOccupation_mono e hU y₀ η (μ.map f) 2 hηle).trans
    apply Measure.le_iff.mpr
    intro S hS
    simpa only [Measure.smul_apply, smul_eq_mul] using
      mul_le_mul' (le_refl (2 : ℝ≥0∞))
        ((meanPhysicalOccupation_map_collar_le e hU y₀ π hπ.measurable he
          μ f hfm V hV.measurableSet hgood) S)

  · intro H hH
    apply mean_subarc_intersections_le μ η f hfm _ hηle hH
    exact hgood.mono fun _ h => h.2.2.1

theorem exists_compact_physical_arc_law_with_intersections
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : G, π y.val = (e y).val)
    (μ : ProbabilityMeasure C(PathTime, Sphere)) (V : Set Sphere) (hV : IsOpen V)
    (b : Sphere)
    (hμ : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V ∧ γ ⊤ = b ∧ physicalDomainLength e y₀ γ < ∞) :
    ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere)),
      IsCompact K ∧
      (∀ α ∈ K, α ∈ terminalArcSet V b ∧ physicalDomainLength e y₀ α < ∞) ∧
      (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
      (∀ x, pathHitProbability η x ≤ 2 * pathHitProbability μ x) ∧
      (∀ x ∉ closure V, pathHitProbability η x = 0) ∧
      meanPhysicalOccupation e y₀ η ≤
        (2 : ℝ≥0∞) • (meanPhysicalOccupation e y₀ μ).restrict (π ⁻¹' V) ∧
      ∀ H : Set Sphere, IsClosed H →
        (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, Sphere))) ≤
          2 * ∫⁻ γ, pathImageCount H γ ∂(μ : Measure C(PathTime, Sphere)) := by
  obtain ⟨K, η, hK, hKS, hη, hhit, hout, hocc, hcounts, _⟩ :=
    exists_compact_physical_arc_law_with_selection hselect harcs e hU y₀ π hπ he μ V hV b hμ
  exact ⟨K, η, hK, hKS, hη, hhit, hout, hocc, hcounts⟩

end CircleDomainRigidity

end

end OAI
