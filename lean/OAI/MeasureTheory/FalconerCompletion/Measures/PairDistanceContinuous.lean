import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.MaskedPushforwardDeficit

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
namespace CurrentFalconer.AssemblyLimit
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {d : ℕ}
lemma pairDistance_continuous : Continuous (@pairDistance d) := continuous_fst.dist continuous_snd
lemma pairWeight_measurable : Measurable (@pairWeight d) :=
  pairDistance_continuous.measurable.pow_const _
noncomputable def weightedOriginalPair (μ ν : Measure (Ambient d)) : Measure (Ambient d × Ambient d) :=
  (μ.prod ν).withDensity (fun z => ENNReal.ofReal (pairWeight z))
lemma filteredDistanceMeasure_eq (μ ν : Measure (Ambient d)) {Γ : Set (Ambient d × Ambient d)}
    (hm : MeasurableSet Γ) :
    filteredDistanceMeasure μ ν Γ = ((weightedOriginalPair μ ν).restrict Γ).map pairDistance := by
  unfold filteredDistanceMeasure weightedOriginalPair
  rw [restrict_withDensity hm]
  congr 1
  rw [←withDensity_indicator hm]
  congr 1
  funext z
  by_cases hz : z∈Γ <;> simp [hz]
lemma original_pair_ae (μ ν : Measure (Ambient d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E₁ E₂ : Set (Ambient d)) (hμ : μ E₁ᶜ=0) (hν : ν E₂ᶜ=0) :
    ∀ᵐ z ∂μ.prod ν, z.1∈E₁ ∧ z.2∈E₂ := by
  have h1 : ∀ᵐ x ∂μ, x∈E₁ := by simpa only [mem_compl_iff,not_not] using (measure_eq_zero_iff_ae_notMem.mp hμ)
  have h2 : ∀ᵐ y ∂ν, y∈E₂ := by simpa only [mem_compl_iff,not_not] using (measure_eq_zero_iff_ae_notMem.mp hν)
  exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
lemma weightedOriginalPair_finite (hd : 2≤d)
    (μ ν : Measure (Ambient d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E₁ E₂ : Set (Ambient d)) (hμ : μ E₁ᶜ=0) (hν : ν E₂ᶜ=0)
    (δ : ℝ) (hδ : 0<δ) (hsep : ∀ x∈E₁, ∀ y∈E₂, δ≤dist x y) :
    IsFiniteMeasure (weightedOriginalPair μ ν) := by
  have he : -((d:ℝ)-1)/2 ≤ 0 := by
    have : (2:ℝ)≤d := by exact_mod_cast hd
    linarith
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    (∫⁻ z, ENNReal.ofReal (pairWeight z) ∂μ.prod ν) ≤
      ∫⁻ z : Ambient d × Ambient d, ENNReal.ofReal (δ^(-((d:ℝ)-1)/2)) ∂μ.prod ν := by
        apply lintegral_mono_ae
        filter_upwards [original_pair_ae μ ν E₁ E₂ hμ hν] with z hz
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hδ (hsep z.1 hz.1 z.2 hz.2) he)
    _ < ∞ := by simp
lemma originalPair_ac_weighted (μ ν : Measure (Ambient d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E₁ E₂ : Set (Ambient d)) (hμ : μ E₁ᶜ=0) (hν : ν E₂ᶜ=0)
    (δ : ℝ) (hδ : 0<δ) (hsep : ∀ x∈E₁, ∀ y∈E₂, δ≤dist x y) :
    μ.prod ν ≪ weightedOriginalPair μ ν := by
  apply withDensity_absolutelyContinuous' pairWeight_measurable.ennreal_ofReal.aemeasurable
  filter_upwards [original_pair_ae μ ν E₁ E₂ hμ hν] with z hz
  exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (hδ.trans_le (hsep z.1 hz.1 z.2 hz.2)) _)).ne'
lemma distanceSet_compact {E : Set (Ambient d)} (hE : IsCompact E) : IsCompact (distanceSet E) := by
  have he : distanceSet E = pairDistance '' (E ×ˢ E) := by
    ext r
    constructor
    · rintro ⟨x,hx,y,hy,hr⟩
      exact ⟨(x,y),⟨hx,hy⟩,hr⟩
    · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,hr⟩
      exact ⟨x,hx,y,hy,hr⟩
  rw [he]
  exact (hE.prod hE).image pairDistance_continuous
lemma filteredDistanceMeasure_carried (μ ν : Measure (Ambient d))
    {E E₁ E₂ : Set (Ambient d)} (hE : IsCompact E) (h₁E : E₁⊆E) (h₂E : E₂⊆E)
    {Γ : Set (Ambient d × Ambient d)} (hm : MeasurableSet Γ) (hs : Γ⊆E₁×ˢE₂) :
    filteredDistanceMeasure μ ν Γ (distanceSet E)ᶜ=0 := by
  rw [filteredDistanceMeasure_eq μ ν hm,Measure.map_apply pairDistance_continuous.measurable
    (distanceSet_compact hE).measurableSet.compl,Measure.restrict_apply
      (pairDistance_continuous.measurable (distanceSet_compact hE).measurableSet.compl)]
  have he : pairDistance ⁻¹' (distanceSet E)ᶜ ∩ Γ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1 ⟨z.1,h₁E (hs hz.2).1,z.2,h₂E (hs hz.2).2,rfl⟩
  rw [he,measure_empty]

end CurrentFalconer.AssemblyLimit
end
end

end OAI
