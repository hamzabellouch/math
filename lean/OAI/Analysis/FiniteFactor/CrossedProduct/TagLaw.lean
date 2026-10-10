import OAI.Analysis.FiniteFactor.CrossedProduct.TagGeometry
import OAI.Analysis.FiniteFactor.Coupling.Order

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal
noncomputable section

namespace CouplingParameters

def tagGood (p : CouplingParameters) : Set (Fin 6 × (ℝ × ℝ)) :=
  {z | z.1 = 5 → z.2.1 < 1/p.m ∧ 1-1/p.m ≤ z.2.2}

theorem tagGood_measurable (p : CouplingParameters) : MeasurableSet p.tagGood := by
  have hlabel : MeasurableSet {z : Fin 6 × (ℝ × ℝ) | z.1 = 5} :=
    (measurableSet_singleton (5 : Fin 6)).preimage measurable_fst
  have hpair : MeasurableSet {z : Fin 6 × (ℝ × ℝ) | z.2.1 < 1/p.m ∧ 1-1/p.m ≤ z.2.2} :=
    (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
    (measurableSet_le measurable_const (measurable_snd.comp measurable_snd))
  convert hlabel.compl.union hpair using 1
  ext z
  simp only [tagGood,Set.mem_ofPred_eq,Set.mem_union,Set.mem_compl_iff,imp_iff_not_or]

theorem labelledCoupling_tag_support (p : CouplingParameters) :
    ∀ᵐ z ∂p.labelledCoupling, z.1 = 5 → z.2.1 < 1/p.m ∧ 1-1/p.m ≤ z.2.2 := by
  have hmap (i : Fin 6) : ((p.pairComponentLaw i).map (fun xy => (i,xy))) p.tagGood = 1 := by
    have hmeas : Measurable (fun xy : ℝ × ℝ => (i,xy)) := measurable_const.prodMk measurable_id
    rw [Measure.map_apply hmeas (tagGood_measurable p)]
    by_cases hi : i = 5
    · subst i
      have hsub : p.endpointInterval false 4 ×ˢ p.endpointInterval true 4 ⊆
          (fun xy : ℝ × ℝ => ((5 : Fin 6),xy)) ⁻¹' p.tagGood := by
        intro xy hxy _
        exact ⟨hxy.1.2,hxy.2.1⟩
      apply le_antisymm prob_le_one
      have hh := measure_mono (μ := p.pairComponentLaw 5) hsub
      have hmass : p.pairComponentLaw 5 (p.endpointInterval false 4 ×ˢ p.endpointInterval true 4) = 1 := by
        change ((p.endpointComponentLaw false 4).prod (p.endpointComponentLaw true 4)) _ = 1
        rw [Measure.prod_prod,p.endpointComponentLaw_of_contains false 4 (Set.Subset.refl _),
          p.endpointComponentLaw_of_contains true 4 (Set.Subset.refl _),mul_one]
      rwa [hmass] at hh
    · have he : (fun xy : ℝ × ℝ => (i,xy)) ⁻¹' p.tagGood = Set.univ := by
        ext xy
        simp [tagGood,hi]
      rw [he,measure_univ]
  have hm : p.labelledCoupling p.tagGood = 1 := by
    rw [labelledCoupling,Measure.finsetSum_apply]
    simp only [Measure.smul_apply,smul_eq_mul,hmap,mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.labelMass_nonneg i),p.labelMass_sum]
    simp
  rw [ae_iff]
  change p.labelledCoupling p.tagGoodᶜ = 0
  rw [measure_compl (tagGood_measurable p) (measure_ne_top _ _),measure_univ,hm,tsub_self]

end CouplingParameters

def sourceTaggedEvent (j : ℕ) : Set SourceBiasedSample :=
  {ω | ∃ i : Fin (sourceBlockSize j), (ω ⟨j,i⟩).1 = 5}

theorem sourceTaggedEvent_measurable (j : ℕ) : MeasurableSet (sourceTaggedEvent j) := by
  have he : sourceTaggedEvent j = ⋃ i : Fin (sourceBlockSize j), {ω : SourceBiasedSample | (ω ⟨j,i⟩).1 = 5} := by
    ext ω
    simp [sourceTaggedEvent]
  rw [he]
  exact MeasurableSet.iUnion fun i => (measurableSet_singleton (5 : Fin 6)).preimage
    (measurable_fst.comp (measurable_pi_apply (⟨j,i⟩ : SourceCoordinate)))

/-- The actual labelled event has the geometric endpoint consequence needed
by every near-range ratio bound, under the original augmented biased law. -/
theorem sourceTaggedEvent_endpoints (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceTaggedEvent j → ω ∈ sourceTagEndpointEvent j := by
  have h (i : Fin (sourceBlockSize j)) : ∀ᵐ ω ∂sourceBiasedLaw j,
      (ω ⟨j,i⟩).1 = 5 → (ω ⟨j,i⟩).2.1 < 1/(sourceBlockSize j : ℝ) ∧
        1-1/(sourceBlockSize j : ℝ) ≤ (ω ⟨j,i⟩).2.2 :=
    (measurePreserving_eval_infinitePi
      (fun i : SourceCoordinate => (stagedCouplingParameters j i.1).labelledCoupling) ⟨j,i⟩).quasiMeasurePreserving.ae
      (labelledCoupling_tag_support (stagedCouplingParameters j j))
  filter_upwards [ae_all_iff.mpr h] with ω hω
  rintro ⟨i,hi⟩
  exact ⟨i,hω i hi⟩

end
end FiniteFactor

end OAI
