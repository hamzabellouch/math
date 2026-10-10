import OAI.Analysis.CircleDomains.Selection.TagDelay
import OAI.Analysis.CircleDomains.Selection.ResidualPieceAssembly

namespace OAI

/-! Clip tags to the interior of a retained parameter interval and discard
the constant restrictions. Their newly exposed image is countable. -/

open Set Function MeasureTheory
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

def clipTag (a b : PathTime) : TagSlot → TagSlot
  | Sum.inl u => Sum.inl u
  | Sum.inr t => Sum.inr ⟨t.1, t.2.1, t.2.2.1,
      max a t.2.2.2.1, min b t.2.2.2.2⟩

theorem tagLeft_clipTag (a b : PathTime) (τ : TagSlot) :
    tagLeft (clipTag a b τ) = max a (tagLeft τ) := by
  cases τ <;> simp [clipTag, tagLeft]

theorem tagRight_clipTag (a b : PathTime) (τ : TagSlot) :
    tagRight (clipTag a b τ) = min b (tagRight τ) := by
  cases τ <;> simp [clipTag, tagRight]

theorem mem_clippedTagInterval (a b t : PathTime) (τ : TagSlot) :
    t ∈ Ioo (tagLeft (clipTag a b τ)) (tagRight (clipTag a b τ)) ↔
      t ∈ Ioo a b ∧ t ∈ Ioo (tagLeft τ) (tagRight τ) := by
  rw [tagLeft_clipTag, tagRight_clipTag]
  simp only [mem_Ioo, max_lt_iff, lt_min_iff]
  tauto

variable {X : Type*} [MetricSpace X]

def narrowTag (γ : C(PathTime, X)) (a b : PathTime) (τ : TagSlot) : TagSlot :=
  if (γ, clipTag a b τ) ∈ nonconstantTagSegment then clipTag a b τ else inactiveTag

def narrowTaggedPath (a b : PathTime) (Γ : TaggedPath X) : TaggedPath X :=
  (Γ.1, fun k => narrowTag Γ.1 a b (Γ.2 k))

theorem narrowTag_interval_subset (γ : C(PathTime, X)) (a b : PathTime) (τ : TagSlot) :
    Ioo (tagLeft (narrowTag γ a b τ)) (tagRight (narrowTag γ a b τ)) ⊆
      Ioo a b ∩ Ioo (tagLeft τ) (tagRight τ) := by
  intro t ht
  by_cases h : (γ, clipTag a b τ) ∈ nonconstantTagSegment
  · rw [narrowTag, ite_eq_left h] at ht
    exact (mem_clippedTagInterval a b t τ).mp ht
  · rw [narrowTag, ite_eq_right h] at ht
    exact False.elim (not_lt_of_ge le_top ht.1)

theorem residualTimes_subset_narrow (B : Set X) (a b : PathTime) (Γ : TaggedPath X) :
    residualTimes B Γ ⊆ residualTimes B (narrowTaggedPath a b Γ) := by
  rw [residualTimes_eq, residualTimes_eq]
  rintro t ⟨ht, hnot⟩
  refine ⟨ht, ?_⟩
  intro h
  obtain ⟨k, hk⟩ := mem_iUnion.mp h
  exact hnot (mem_iUnion.mpr ⟨k, (narrowTag_interval_subset Γ.1 a b (Γ.2 k) hk).2⟩)

theorem discarded_clip_image_countable (γ : C(PathTime, X)) (a b : PathTime)
    (τ : TagSlot) (h : (γ, clipTag a b τ) ∉ nonconstantTagSegment) :
    (γ '' Ioo (tagLeft (clipTag a b τ)) (tagRight (clipTag a b τ))).Countable := by
  apply Set.Subsingleton.countable
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
  by_contra hne
  exact h ⟨s, t, hs.1, hs.2, ht.1, ht.2, hne⟩

theorem newly_exposed_narrow_image_countable (B : Set X) (a b : PathTime)
    (Γ : TaggedPath X) :
    (Γ.1 '' ((residualTimes B (narrowTaggedPath a b Γ) ∩ Ioo a b) \
      residualTimes B Γ)).Countable := by
  let A : ℕ → Set X := fun k => if (Γ.1, clipTag a b (Γ.2 k)) ∈ nonconstantTagSegment
    then ∅ else Γ.1 '' Ioo (tagLeft (clipTag a b (Γ.2 k)))
      (tagRight (clipTag a b (Γ.2 k)))
  have hA : (⋃ k, A k).Countable := by
    apply Set.countable_iUnion
    intro k
    dsimp only [A]
    split_ifs with hk
    · exact countable_empty
    · exact discarded_clip_image_countable Γ.1 a b (Γ.2 k) hk
  apply hA.mono
  rintro x ⟨t, ⟨⟨ht, hab⟩, hold⟩, rfl⟩
  have hdust : Γ.1 t ∈ B := ht.1
  have hcovered : ∃ k, t ∈ Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) := by
    by_contra h
    apply hold
    refine ⟨hdust, fun k => ?_⟩
    have hk : ¬ (tagLeft (Γ.2 k) < t ∧ t < tagRight (Γ.2 k)) :=
      fun hk => h ⟨k, hk⟩
    exact (not_and_or.mp hk).imp le_of_not_gt le_of_not_gt
  obtain ⟨k, hk⟩ := hcovered
  have hc : t ∈ Ioo (tagLeft (clipTag a b (Γ.2 k)))
      (tagRight (clipTag a b (Γ.2 k))) :=
    (mem_clippedTagInterval a b t (Γ.2 k)).mpr ⟨hab, hk⟩
  have hn : (Γ.1, clipTag a b (Γ.2 k)) ∉ nonconstantTagSegment := by
    intro hn
    have ht' := ht.2 k
    change t ≤ tagLeft (narrowTag Γ.1 a b (Γ.2 k)) ∨
      tagRight (narrowTag Γ.1 a b (Γ.2 k)) ≤ t at ht'
    rw [narrowTag, ite_eq_left hn] at ht'
    exact ht'.elim (not_le_of_gt hc.1) (not_le_of_gt hc.2)
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  dsimp only [A]
  rw [ite_eq_right hn]
  exact ⟨t, hc, rfl⟩

end CircleDomainRigidity

end

end OAI
