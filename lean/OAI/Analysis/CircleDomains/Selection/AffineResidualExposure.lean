import OAI.Analysis.CircleDomains.Selection.AffineTagRestriction

namespace OAI

/-! Under affine restriction, old residual times remain residual. Discarded
constant tags expose only countably many image points in the open piece. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem affine_old_residual_subset (B : Set X) {a b : PathTime} (hab : a < b)
    (Γ : TaggedPath X) :
    affinePathTime a b ⁻¹' residualTimes B Γ ⊆
      residualTimes B (affineRestrictedTaggedPath a b Γ) := by
  intro t ht
  refine ⟨ht.1, fun k => ?_⟩
  by_cases hn : (affineRestrictedPath a b Γ.1, affineRawTag a b (Γ.2 k)) ∈ nonconstantTagSegment
  · change t ≤ tagLeft (affineRestrictedTag a b Γ.1 (Γ.2 k)) ∨
      tagRight (affineRestrictedTag a b Γ.1 (Γ.2 k)) ≤ t
    rw [affineRestrictedTag, ite_eq_left hn]
    by_contra h
    push Not at h
    have htime : ⊥ < t ∧ t < ⊤ := ⟨lt_of_le_of_lt bot_le h.1, lt_of_lt_of_le h.2 le_top⟩
    have hold := (affineRawTag_interval hab (Γ.2 k) htime).mp h
    exact (ht.2 k).elim (not_le_of_gt hold.1) (not_le_of_gt hold.2)
  · left
    change t ≤ tagLeft (affineRestrictedTag a b Γ.1 (Γ.2 k))
    rw [affineRestrictedTag, ite_eq_right hn]
    exact le_top

theorem affine_discarded_image_countable (a b : PathTime) (Γ : TaggedPath X)
    (k : ℕ)
    (hn : (affineRestrictedPath a b Γ.1, affineRawTag a b (Γ.2 k)) ∉ nonconstantTagSegment) :
    (affineRestrictedPath a b Γ.1 '' Ioo (tagLeft (affineRawTag a b (Γ.2 k)))
      (tagRight (affineRawTag a b (Γ.2 k)))).Countable := by
  apply Set.Subsingleton.countable
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
  by_contra hne
  exact hn ⟨s, t, hs.1, hs.2, ht.1, ht.2, hne⟩

theorem affine_exposed_image_countable (B : Set X) {a b : PathTime} (hab : a < b)
    (Γ : TaggedPath X) :
    (affineRestrictedPath a b Γ.1 ''
      ((residualTimes B (affineRestrictedTaggedPath a b Γ) ∩ Ioo ⊥ ⊤) \
        (affinePathTime a b ⁻¹' residualTimes B Γ))).Countable := by
  let A : ℕ → Set X := fun k =>
    if (affineRestrictedPath a b Γ.1, affineRawTag a b (Γ.2 k)) ∈ nonconstantTagSegment
    then ∅ else affineRestrictedPath a b Γ.1 ''
      Ioo (tagLeft (affineRawTag a b (Γ.2 k))) (tagRight (affineRawTag a b (Γ.2 k)))
  have hA : (⋃ k, A k).Countable := by
    apply Set.countable_iUnion
    intro k
    dsimp only [A]
    split_ifs with hk
    · exact countable_empty
    · exact affine_discarded_image_countable a b Γ k hk
  apply hA.mono
  rintro x ⟨t, ⟨⟨ht, htime⟩, hold⟩, rfl⟩
  have hdust : Γ.1 (affinePathTime a b t) ∈ B := ht.1
  have hcovered : ∃ k, affinePathTime a b t ∈ Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) := by
    by_contra h
    apply hold
    refine ⟨hdust, fun k => ?_⟩
    have hk : ¬ (tagLeft (Γ.2 k) < affinePathTime a b t ∧
        affinePathTime a b t < tagRight (Γ.2 k)) := fun hk => h ⟨k, hk⟩
    exact (not_and_or.mp hk).imp le_of_not_gt le_of_not_gt
  obtain ⟨k, hk⟩ := hcovered
  have hc := (affineRawTag_interval hab (Γ.2 k) htime).mpr hk
  have hn : (affineRestrictedPath a b Γ.1, affineRawTag a b (Γ.2 k)) ∉ nonconstantTagSegment := by
    intro hn
    have ht' := ht.2 k
    change t ≤ tagLeft (affineRestrictedTag a b Γ.1 (Γ.2 k)) ∨
      tagRight (affineRestrictedTag a b Γ.1 (Γ.2 k)) ≤ t at ht'
    rw [affineRestrictedTag, ite_eq_left hn] at ht'
    exact ht'.elim (not_le_of_gt hc.1) (not_le_of_gt hc.2)
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  dsimp only [A]
  rw [ite_eq_right hn]
  exact ⟨t, hc, rfl⟩

end CircleDomainRigidity

end

end OAI
