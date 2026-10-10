import OAI.Analysis.CircleDomains.Selection.NarrowedTags

namespace OAI

/-! Narrowing a tag changes only its time interval. Every retained tag has
the original level tuple and continues to obey the level and null-set rules. -/

open Set
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

theorem active_mem_tagTupleExcluded_iff
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (q : TagData) : (Sum.inr q : TagSlot) ∈ tagTupleExcluded N ↔ q.2.2.1 ∈ N q.1 q.2.1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    obtain ⟨l, p, hp, he⟩ := mem_iUnion.mp hn
    have hq : (⟨n, l, p⟩ : TagData) = q := Sum.inr.inj he
    cases hq
    exact hp.1
  · intro h
    exact mem_iUnion.mpr ⟨q.1, mem_iUnion.mpr ⟨q.2.1, q.2.2, ⟨h, mem_univ _⟩, rfl⟩⟩

theorem clipTag_tuple_excluded_iff
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (a b : PathTime) (τ : TagSlot) :
    clipTag a b τ ∈ tagTupleExcluded N ↔ τ ∈ tagTupleExcluded N := by
  cases τ with
  | inl u => rfl
  | inr q =>
    exact (active_mem_tagTupleExcluded_iff N
      ⟨q.1, q.2.1, q.2.2.1, max a q.2.2.2.1, min b q.2.2.2.2⟩).trans
        (active_mem_tagTupleExcluded_iff N q).symm

variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem clipTag_level_iff (H : ℕ → Set (UnitAddCircle × X))
    (a b : PathTime) (τ : TagSlot) (x : X) :
    (clipTag a b τ, x) ∈ tagLevelGraph H ↔ (τ, x) ∈ tagLevelGraph H := by
  cases τ <;> rfl

theorem narrowTag_rules (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (a b : PathTime) (τ : TagSlot)
    (hc : (γ, τ) ∈ tagContainment H) (hn : τ ∉ tagTupleExcluded N) :
    (γ, narrowTag γ a b τ) ∈ validTagShape ∧
      (γ, narrowTag γ a b τ) ∈ tagContainment H ∧
      narrowTag γ a b τ ∉ tagTupleExcluded N := by
  by_cases h : (γ, clipTag a b τ) ∈ nonconstantTagSegment
  · rw [narrowTag, ite_eq_left h]
    refine ⟨Or.inr h, ?_, fun hN => hn ((clipTag_tuple_excluded_iff N a b τ).mp hN)⟩
    intro t hl hr
    have ht := (mem_clippedTagInterval a b t τ).mp ⟨hl, hr⟩
    exact (clipTag_level_iff H a b τ (γ t)).mpr (hc t ht.2.1 ht.2.2)
  · rw [narrowTag, ite_eq_right h]
    exact inactiveTag_rules H N γ

theorem tagRules_narrow (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (a b : PathTime) (Γ : TaggedPath X) (hΓ : TagRules H N Γ) :
    TagRules H N (narrowTaggedPath a b Γ) := by
  intro k
  exact narrowTag_rules H N Γ.1 a b (Γ.2 k) (hΓ k).2.1 (hΓ k).2.2

end CircleDomainRigidity

end

end OAI
