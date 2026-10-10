import OAI.Analysis.CircleDomains.Sobolev.SobolevLevelOscillation
import OAI.Analysis.CircleDomains.Probability.NullImage
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! A zero weighted trace on a compact locally connected finite-length
level has null scalar image. The weight and all oscillations come from
the actual smooth approximations, not from a null-image hypothesis. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finite_level_null_image_of_approximation
    {K F : Set ℂ} (hK : IsCompact K) (hKfin : (μH[1] : Measure ℂ) K < ∞)
    [LocallyConnectedSpace K]
    (u : ℕ → ℂ → ℝ) (hu : ∀ n, ContDiff ℝ 1 (u n)) {v : ℂ → ℝ}
    (hv : ∀ z ∈ K, Tendsto (fun n => u n z) atTop (𝓝 (v z)))
    (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    (hgfin : (∫⁻ z in K, g z ∂(μH[1] : Measure ℂ)) < ∞)
    (hF : MeasurableSet F)
    (hgF : (∫⁻ z in F ∩ K, g z ∂(μH[1] : Measure ℂ)) = 0)
    (e : ℕ → ℂ → ℝ≥0∞)
    (hgrad : ∀ n, ∀ᵐ z ∂(μH[1] : Measure ℂ).restrict K,
      ENNReal.ofReal ‖fderiv ℝ (u n) z‖ ≤ g z+e n z)
    (herror : Tendsto (fun n => ∫⁻ z in K, e n z ∂(μH[1] : Measure ℂ)) atTop (𝓝 0)) :
    volume (v '' (F ∩ K)) = 0 := by
  let μ : Measure ℂ := ((μH[1] : Measure ℂ).restrict K).withDensity g
  let : IsFiniteMeasure μ := ⟨by
    change ((μH[1] : Measure ℂ).restrict K).withDensity g univ < ∞
    simpa only [withDensity_apply g MeasurableSet.univ, Measure.restrict_univ] using hgfin⟩
  have hμ (A : Set ℂ) (hA : MeasurableSet A) (hAK : A ⊆ K) :
      μ A = ∫⁻ z in A, g z ∂(μH[1] : Measure ℂ) := by
    rw [show μ = ((μH[1] : Measure ℂ).restrict K).withDensity g from rfl,
      withDensity_apply g hA, Measure.restrict_restrict hA, inter_eq_left.mpr hAK]
  have hμF : μ (F ∩ K) = 0 := by
    rw [hμ _ (hF.inter hK.isClosed.measurableSet) inter_subset_right, hgF]
  have hemb : MeasurableEmbedding (Subtype.val : K → ℂ) :=
    MeasurableEmbedding.subtype_coe hK.isClosed.measurableSet
  let ν : Measure K := μ.comap Subtype.val
  let : IsFiniteMeasure ν := ⟨by
    change μ.comap Subtype.val univ < ∞
    rw [hemb.comap_apply]
    exact measure_lt_top μ _⟩
  have hν (A : Set K) (hA : MeasurableSet A) :
      ν A = ∫⁻ z in Subtype.val '' A, g z ∂(μH[1] : Measure ℂ) := by
    rw [show ν = μ.comap Subtype.val from rfl, hemb.comap_apply]
    exact hμ _ (hemb.measurableSet_image.mpr hA) (by rintro _ ⟨z, _, rfl⟩; exact z.property)
  have hνF : ν (Subtype.val ⁻¹' F) = 0 := by
    change μ.comap Subtype.val (Subtype.val ⁻¹' F) = 0
    rw [hemb.comap_apply, Subtype.image_preimage_coe, inter_comm, hμF]
  have hn := null_image_of_connected_open_oscillation (μ := ν) hνF
    (fun z : K => v z.val) (by norm_num : (0 : ℝ) ≤ 1) (by
      intro A hA hc x hx y hy
      have hAK : Subtype.val '' A ⊆ K := by rintro _ ⟨z, _, rfl⟩; exact z.property
      have hp := connected_level_oscillation_of_approximation hKfin u hu hv g hg e hgrad herror
        (hemb.measurableSet_image.mpr hA.measurableSet) hAK
        (hc.isPreconnected.image Subtype.val continuous_subtype_val.continuousOn)
        (mem_image_of_mem Subtype.val hx.2) (mem_image_of_mem Subtype.val hy.2)
      rw [← hν A hA.measurableSet] at hp
      have hr := ENNReal.toReal_mono (measure_ne_top ν A) hp
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def, one_mul] using hr)
  have himage : (fun z : K => v z.val) '' (Subtype.val ⁻¹' F) = v '' (F ∩ K) := by
    ext t
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.val, ⟨hz, z.property⟩, rfl⟩
    · rintro ⟨z, ⟨hzF, hzK⟩, rfl⟩
      exact ⟨⟨z, hzK⟩, hzF, rfl⟩
  rwa [himage] at hn

end CircleDomainRigidity

end

end OAI
