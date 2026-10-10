import OAI.Analysis.CircleDomains.Selection.AffineTagRestriction
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Transport the tags of one path into an open piece of a larger path.
Every transported tag stays inside that piece and retains its level tuple. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

def embeddedTag (a b : PathTime) : TagSlot → TagSlot
  | Sum.inl u => Sum.inl u
  | Sum.inr q => Sum.inr ⟨q.1, q.2.1, q.2.2.1,
      affinePathTime a b q.2.2.2.1, affinePathTime a b q.2.2.2.2⟩

theorem embeddedTag_interval {a b : PathTime} (hab : a < b) (τ : TagSlot) :
    Ioo (tagLeft (embeddedTag a b τ)) (tagRight (embeddedTag a b τ)) =
      affinePathTime a b '' Ioo (tagLeft τ) (tagRight τ) := by
  cases τ with
  | inl u => simp [embeddedTag, tagLeft, tagRight]
  | inr q => exact ((affinePathTime a b).continuous.image_Ioo_of_strictMono
      (affinePathTime_strictMono hab)).symm

theorem embeddedTag_interval_subset {a b : PathTime} (hab : a < b) (τ : TagSlot) :
    Ioo (tagLeft (embeddedTag a b τ)) (tagRight (embeddedTag a b τ)) ⊆ Ioo a b := by
  rw [embeddedTag_interval hab]
  rintro t ⟨s, hs, rfl⟩
  have hleft : (⊥ : PathTime) < s := lt_of_le_of_lt bot_le hs.1
  have hright : s < (⊤ : PathTime) := lt_of_lt_of_le hs.2 le_top
  change a < affinePathTime a b s ∧ affinePathTime a b s < b
  simpa only [affinePathTime_zero, affinePathTime_one] using
    And.intro (affinePathTime_strictMono hab hleft) (affinePathTime_strictMono hab hright)

theorem embeddedTag_tuple_excluded_iff
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (a b : PathTime) (τ : TagSlot) :
    embeddedTag a b τ ∈ tagTupleExcluded N ↔ τ ∈ tagTupleExcluded N := by
  cases τ with
  | inl u => rfl
  | inr q =>
    exact (active_mem_tagTupleExcluded_iff N
      ⟨q.1, q.2.1, q.2.2.1, affinePathTime a b q.2.2.2.1,
        affinePathTime a b q.2.2.2.2⟩).trans (active_mem_tagTupleExcluded_iff N q).symm

variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem embeddedTag_level_iff (H : ℕ → Set (UnitAddCircle × X))
    (a b : PathTime) (τ : TagSlot) (x : X) :
    (embeddedTag a b τ, x) ∈ tagLevelGraph H ↔ (τ, x) ∈ tagLevelGraph H := by
  cases τ <;> rfl

theorem embeddedTag_rules (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    {a b : PathTime} (hab : a < b) (γ η : C(PathTime, X))
    (he : ∀ t ∈ Ioo (⊥ : PathTime) ⊤, η (affinePathTime a b t) = γ t)
    (τ : TagSlot) (hshape : (γ, τ) ∈ validTagShape)
    (hcontain : (γ, τ) ∈ tagContainment H) (hN : τ ∉ tagTupleExcluded N) :
    (η, embeddedTag a b τ) ∈ validTagShape ∧
      (η, embeddedTag a b τ) ∈ tagContainment H ∧
      embeddedTag a b τ ∉ tagTupleExcluded N := by
  refine ⟨?_, ?_, fun hn => hN ((embeddedTag_tuple_excluded_iff N a b τ).mp hn)⟩
  · rcases hshape with hinactive | hnonconstant
    · obtain ⟨u, rfl⟩ := hinactive
      exact Or.inl ⟨u, rfl⟩
    · obtain ⟨s, t, hsl, hsr, htl, htr, hne⟩ := hnonconstant
      have hs : s ∈ Ioo (⊥ : PathTime) ⊤ :=
        ⟨lt_of_le_of_lt bot_le hsl, lt_of_lt_of_le hsr le_top⟩
      have ht : t ∈ Ioo (⊥ : PathTime) ⊤ :=
        ⟨lt_of_le_of_lt bot_le htl, lt_of_lt_of_le htr le_top⟩
      have hsi : affinePathTime a b s ∈
          Ioo (tagLeft (embeddedTag a b τ)) (tagRight (embeddedTag a b τ)) := by
        rw [embeddedTag_interval hab]
        exact ⟨s, ⟨hsl, hsr⟩, rfl⟩
      have hti : affinePathTime a b t ∈
          Ioo (tagLeft (embeddedTag a b τ)) (tagRight (embeddedTag a b τ)) := by
        rw [embeddedTag_interval hab]
        exact ⟨t, ⟨htl, htr⟩, rfl⟩
      exact Or.inr ⟨_, _, hsi.1, hsi.2, hti.1, hti.2, by rwa [he s hs, he t ht]⟩
  · intro t hl hr
    have ht : t ∈ Ioo (tagLeft (embeddedTag a b τ)) (tagRight (embeddedTag a b τ)) := ⟨hl, hr⟩
    rw [embeddedTag_interval hab] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have hsi : s ∈ Ioo (⊥ : PathTime) ⊤ :=
      ⟨lt_of_le_of_lt bot_le hs.1, lt_of_lt_of_le hs.2 le_top⟩
    rw [he s hsi]
    exact (embeddedTag_level_iff H a b τ _).mpr (hcontain s hs.1 hs.2)

end CircleDomainRigidity

end

end OAI
