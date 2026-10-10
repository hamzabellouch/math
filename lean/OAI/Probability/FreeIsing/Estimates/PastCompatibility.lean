import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Problem367

lemma setIntegral_independent_future
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {mPast mFuture : MeasurableSpace Ω}
    (hPast : mPast ≤ m) (hFuture : mFuture ≤ m)
    (hIndep : Indep mPast mFuture μ)
    {f : Ω → ℝ} (hf : StronglyMeasurable[mPast] f) (hfint : Integrable f μ)
    {s t : Set Ω} (hs : MeasurableSet[mPast] s) (ht : MeasurableSet[mFuture] t) :
    (∫ x in s ∩ t, f x ∂μ) = μ.real t * ∫ x in s, f x ∂μ := by
  have hce := condExp_indep_eq hPast hFuture (hf.indicator hs) hIndep
  have hit : Integrable (s.indicator f) μ := hfint.indicator (hPast _ hs)
  have hse := setIntegral_condExp hFuture hit ht
  have hcongr := setIntegral_congr_ae (hFuture _ ht)
    (hce.mono (fun x hx _ => hx))
  rw [hse] at hcongr
  rw [setIntegral_indicator (hPast _ hs), integral_indicator (hPast _ hs),
    setIntegral_const, smul_eq_mul, Set.inter_comm] at hcongr
  exact hcongr

lemma measurable_sup_eq_generate_intersections
    {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    m₁ ⊔ m₂ = MeasurableSpace.generateFrom
      {u | ∃ s t, MeasurableSet[m₁] s ∧ MeasurableSet[m₂] t ∧ u = s ∩ t} := by
  apply le_antisymm
  · apply sup_le
    · intro s hs
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨s, Set.univ, hs, MeasurableSet.univ, by simp⟩
    · intro t ht
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨Set.univ, t, MeasurableSet.univ, ht, by simp⟩
  · apply MeasurableSpace.generateFrom_le
    rintro u ⟨s, t, hs, ht, rfl⟩
    exact ((show m₁ ≤ m₁ ⊔ m₂ from le_sup_left) s hs).inter
      ((show m₂ ≤ m₁ ⊔ m₂ from le_sup_right) t ht)

lemma isPiSystem_measurable_intersections
    {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    IsPiSystem {u | ∃ s t, MeasurableSet[m₁] s ∧ MeasurableSet[m₂] t ∧ u = s ∩ t} := by
  rintro u ⟨s, t, hs, ht, rfl⟩ v ⟨s', t', hs', ht', rfl⟩ _
  refine ⟨s ∩ s', t ∩ t', hs.inter hs', ht.inter ht', ?_⟩
  ext x
  simp only [Set.mem_inter_iff]
  tauto

lemma condExp_sup_independent_future
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {mSmall mPast mFuture : MeasurableSpace Ω}
    (hSmall : mSmall ≤ mPast) (hPast : mPast ≤ m) (hFuture : mFuture ≤ m)
    (hIndep : Indep mPast mFuture μ)
    {f : Ω → ℝ} (hf : StronglyMeasurable[mPast] f) (hfint : Integrable f μ) :
    μ[f | mSmall ⊔ mFuture] =ᵐ[μ] μ[f | mSmall] := by
  have hSmallAmbient : mSmall ≤ m := hSmall.trans hPast
  have hJoin : mSmall ⊔ mFuture ≤ m := sup_le hSmallAmbient hFuture
  let g : Ω → ℝ := μ[f | mSmall]
  have hgint : Integrable g μ := integrable_condExp
  have hgsm : StronglyMeasurable[mSmall] g := stronglyMeasurable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hJoin hfint
    (fun s _ _ => hgint.integrableOn) ?_
    (hgsm.mono (show mSmall ≤ mSmall ⊔ mFuture from le_sup_left)).aestronglyMeasurable).symm
  intro s hs _
  refine MeasurableSpace.induction_on_inter
    (measurable_sup_eq_generate_intersections mSmall mFuture)
    (isPiSystem_measurable_intersections mSmall mFuture) (by simp) ?_ ?_ ?_ s hs
  · rintro u ⟨a, b, ha, hb, rfl⟩
    rw [setIntegral_independent_future hPast hFuture hIndep (hgsm.mono hSmall)
        hgint (hSmall _ ha) hb,
      setIntegral_independent_future hPast hFuture hIndep hf hfint (hSmall _ ha) hb]
    rw [show (∫ x in a, g x ∂μ) = ∫ x in a, f x ∂μ from
      setIntegral_condExp hSmallAmbient hfint ha]
  · intro a ha heq
    rw [setIntegral_compl (hJoin _ ha) hgint, setIntegral_compl (hJoin _ ha) hfint, heq]
    rw [show (∫ x, g x ∂μ) = ∫ x, f x ∂μ from integral_condExp hSmallAmbient]
  · intro a hdisj ha heq
    rw [integral_iUnion (fun i => hJoin _ (ha i)) hdisj hgint.integrableOn,
      integral_iUnion (fun i => hJoin _ (ha i)) hdisj hfint.integrableOn]
    exact tsum_congr heq

end Problem367

end

end OAI
