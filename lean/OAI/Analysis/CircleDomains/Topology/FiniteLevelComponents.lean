import OAI.Analysis.CircleDomains.Probability.FiniteLevelNullImage
import OAI.Analysis.CircleDomains.Modulus.FiniteLengthTopology

namespace OAI

/-! On a finite-length compact level, the countable nontrivial components
carry every point at which a level continuum has been constructed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finite_level_components_null_image
    {K F : Set ℂ} (hK : IsCompact K) (hKfin : (μH[1] : Measure ℂ) K < ∞)
    (u : ℕ → ℂ → ℝ) (hu : ∀ n, ContDiff ℝ 1 (u n)) {v : ℂ → ℝ}
    (hv : ∀ z ∈ K, Tendsto (fun n => u n z) atTop (𝓝 (v z)))
    (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    (hgfin : (∫⁻ z in K, g z ∂(μH[1] : Measure ℂ)) < ∞)
    (hF : MeasurableSet F)
    (hgF : (∫⁻ z in F ∩ K, g z ∂(μH[1] : Measure ℂ)) = 0)
    (e : ℕ → ℂ → ℝ≥0∞)
    (hgrad : ∀ n, ∀ᵐ z ∂(μH[1] : Measure ℂ).restrict K,
      ENNReal.ofReal ‖fderiv ℝ (u n) z‖ ≤ g z+e n z)
    (herror : Tendsto (fun n => ∫⁻ z in K, e n z ∂(μH[1] : Measure ℂ)) atTop (𝓝 0))
    (hcover : ∀ z (_hzF : z ∈ F) (hzK : z ∈ K),
      (connectedComponent (⟨z, hzK⟩ : K)).Nontrivial) :
    volume (v '' (F ∩ K)) = 0 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set (Set K) := {C | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}
  have hS : S.Countable := countable_nontrivial_connectedComponents (finite_length_subspace_bound hKfin)
  have hnull (C : Set K) (hC : C ∈ S) : volume (v '' (F ∩ (Subtype.val '' C))) = 0 := by
    obtain ⟨⟨x, rfl⟩, _⟩ := hC
    let D : Set ℂ := Subtype.val '' connectedComponent x
    have hDc : IsCompact D := isClosed_connectedComponent.isCompact.image continuous_subtype_val
    have hDconn : IsConnected D := isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
    have hDK : D ⊆ K := by rintro _ ⟨y, _, rfl⟩; exact y.property
    have hDfin : (μH[1] : Measure ℂ) D < ∞ := (measure_mono hDK).trans_lt hKfin
    let : CompactSpace D := isCompact_iff_compactSpace.mp hDc
    let : PreconnectedSpace D := Subtype.preconnectedSpace hDconn.isPreconnected
    let : LocallyConnectedSpace D := locallyConnectedSpace_of_finite_large_continuum_bound
      (finite_length_subspace_bound hDfin)
    apply finite_level_null_image_of_approximation hDc hDfin u hu
      (fun z hz => hv z (hDK hz)) g hg
      ((lintegral_mono_set hDK).trans_lt hgfin) hF ?_ e ?_ ?_
    · apply le_antisymm _ bot_le
      exact (lintegral_mono_set (μ := (μH[1] : Measure ℂ)) (f := g)
        (inter_subset_inter_right F hDK)).trans_eq hgF
    · intro n
      exact (hgrad n).filter_mono (ae_mono (Measure.restrict_mono hDK le_rfl))
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herror
        (fun _ => bot_le) (fun n => lintegral_mono_set hDK)
  have himage : v '' (F ∩ K) ⊆ ⋃ C ∈ S, v '' (F ∩ (Subtype.val '' C)) := by
    rintro _ ⟨z, hz, rfl⟩
    let x : K := ⟨z, hz.2⟩
    refine mem_iUnion.mpr ⟨connectedComponent x, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact ⟨⟨x, rfl⟩, hcover z hz.1 hz.2⟩
    · exact ⟨z, ⟨hz.1, x, mem_connectedComponent, rfl⟩, rfl⟩
  exact measure_mono_null himage ((measure_biUnion_null_iff hS).mpr hnull)

end CircleDomainRigidity

end

end OAI
