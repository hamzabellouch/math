import OAI.Analysis.CircleDomains.Sobolev.PlanarSliceIntegrals

namespace OAI

/-! Interchanging physical coordinate axes preserves area and exchanges
horizontal and vertical fiber tests. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

 def planarAxisSwap (z : ℂ) : ℂ := ⟨z.im, z.re⟩

 theorem continuous_planarAxisSwap : Continuous planarAxisSwap :=
  Complex.equivRealProdCLM.symm.continuous.comp
    (continuous_swap.comp Complex.equivRealProdCLM.continuous)

 @[simp] theorem planarAxisSwap_involutive (z : ℂ) : planarAxisSwap (planarAxisSwap z) = z := rfl

 theorem planarAxisSwap_bijective : Bijective planarAxisSwap :=
  (show Involutive planarAxisSwap from planarAxisSwap_involutive).bijective

 theorem planarAxisSwap_measurePreserving : MeasurePreserving planarAxisSwap := by
  have hs : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
    simpa only [Measure.volume_eq_prod] using
      Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  exact Complex.volume_preserving_equiv_real_prod.symm.comp
    (hs.comp Complex.volume_preserving_equiv_real_prod)

 theorem planarAxisSwap_preimage_box (I J : Set ℝ) :
    planarAxisSwap ⁻¹' planarSliceBox I J = planarSliceBox J I := by
  ext z
  change (z.im ∈ I ∧ z.re ∈ J) ↔ (z.re ∈ J ∧ z.im ∈ I)
  exact and_comm

 theorem planarAxisSwap_image_box (I J : Set ℝ) :
    planarAxisSwap '' planarSliceBox I J = planarSliceBox J I := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw.2, hw.1⟩
  · intro hz
    exact ⟨planarAxisSwap z, ⟨hz.2, hz.1⟩, planarAxisSwap_involutive z⟩

 theorem planarAxisSwap_image_horizontal_fiber (I J : Set ℝ) (x : ℝ) :
    planarAxisSwap '' (planarSliceBox I J ∩ Complex.im ⁻¹' {x}) =
      planarSliceBox J I ∩ Complex.re ⁻¹' {x} := by
  ext z
  constructor
  · rintro ⟨w, ⟨hw, hx⟩, rfl⟩
    exact ⟨⟨hw.2, hw.1⟩, hx⟩
  · rintro ⟨hz, hx⟩
    exact ⟨planarAxisSwap z, ⟨⟨hz.2, hz.1⟩, hx⟩, planarAxisSwap_involutive z⟩

 theorem lintegral_planarAxisSwap_box (I J : Set ℝ) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ) :
    (∫⁻ z in planarSliceBox I J, ρ (planarAxisSwap z)) =
      ∫⁻ z in planarSliceBox J I, ρ z := by
  have hm : MeasurableSet (planarSliceBox J I) :=
    (hJ.preimage Complex.continuous_re.measurable).inter
      (hI.preimage Complex.continuous_im.measurable)
  rw [← planarAxisSwap_preimage_box J I]
  exact planarAxisSwap_measurePreserving.setLIntegral_comp_preimage hm hρ

end CircleDomainRigidity

end

end OAI
