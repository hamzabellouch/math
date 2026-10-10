import OAI.MeasureTheory.Falconer.Estimates.RelativeRegularizationGain
import OAI.MeasureTheory.Falconer.Recursion.IntermediateProfiles

namespace OAI

/-! # Relative recombination in source-first coordinates -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem source_relative_regularization_gain (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G₀ : Set (Space d × Space d)) (hG₀ : MeasurableSet G₀)
    (hroot : μ Q.carrierᶜ = 0) {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N)
    {threshold : ℝ≥0∞} (hthreshold : 0 < threshold) (t C : ℝ≥0∞) (r : ℝ)
    (hlocal : ∀ p ∈ regularizationLeaves Q μ N,
      regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H) threshold →
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        ((sourceClass Q μ N (N/H) p).prod ν) (G₀ \ G) ≤ t ∧
        ∀ x u : Space d, sourceClass Q μ N (N/H) p
          {z | (z,x) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧ G ⊆ G₀ ∧
      (μ.prod ν) (G₀ \ G) ≤ ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*threshold+t ∧
      ∀ x u : Space d, μ {z | (z,x) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  let S := Prod.swap ⁻¹' G₀
  have hS : MeasurableSet S := hG₀.preimage measurable_swap
  have hclasses : ∀ T ∈ regularizationIndex Q μ N (N/H) threshold,
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        (ν.prod (normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T)) (S \ G) ≤ t ∧
        ∀ x u : Space d, normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
    intro T hT
    have hT' := hT
    simp only [regularizationIndex,Finset.mem_filter] at hT'
    obtain ⟨p,hp,hpT⟩ := Finset.mem_image.mp hT'.1
    have : IsProbabilityMeasure (normalizedClass Q μ (regularizationLeaves Q μ N)
        (regularizationLabel Q μ N (N/H)) T) := by
      simpa only [sourceClass,hpT] using regularization_class_probability Q hQ μ N (N/H) hp
    obtain ⟨G,hG,hd,hc⟩ := hlocal p hp (hpT.symm ▸ hT)
    refine ⟨Prod.swap ⁻¹' G,hG.preimage measurable_swap,?_,?_⟩
    · have he : S \ Prod.swap ⁻¹' G = Prod.swap ⁻¹' (G₀ \ G) := rfl
      rw [he,← Measure.map_apply measurable_swap (hG₀.diff hG),Measure.prod_swap]
      simpa only [sourceClass,hpT] using hd
    · simpa only [sourceClass,hpT,mem_preimage,Prod.swap_prod_mk] using hc
  obtain ⟨G,hG,hsub,hd,hc⟩ := relative_regularization_radial_gain Q hQ μ ν S hS
    hroot hH hNH hdN hthreshold t C r hclasses
  refine ⟨Prod.swap ⁻¹' G,hG.preimage measurable_swap,fun z hz => hsub hz,?_,hc⟩
  have he : G₀ \ Prod.swap ⁻¹' G = Prod.swap ⁻¹' (S \ G) := by
    ext z
    simp only [mem_sdiff,mem_preimage,S,Prod.swap_swap]
  rw [he,← Measure.map_apply measurable_swap (hS.diff hG),Measure.prod_swap]
  exact hd

end Falconer.Regularization

end OAI
