import OAI.Analysis.CircleDomains.Topology.AffinePathTime
import OAI.Analysis.CircleDomains.Selection.NarrowedTagRules

namespace OAI

/-! Actual affine restriction of tagged paths. Reparameterized tags keep
their old tuples; empty and constant tag pieces become inactive. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

def affineRawTag (a b : PathTime) : TagSlot → TagSlot
  | Sum.inl u => Sum.inl u
  | Sum.inr q => Sum.inr ⟨q.1, q.2.1, q.2.2.1,
      rescalePathTime a b q.2.2.2.1, rescalePathTime a b q.2.2.2.2⟩

theorem affineRawTag_interval {a b : PathTime} (hab : a < b) (τ : TagSlot)
    {t : PathTime} (ht : ⊥ < t ∧ t < ⊤) :
    t ∈ Ioo (tagLeft (affineRawTag a b τ)) (tagRight (affineRawTag a b τ)) ↔
      affinePathTime a b t ∈ Ioo (tagLeft τ) (tagRight τ) := by
  cases τ with
  | inl u => simp [affineRawTag, tagLeft, tagRight]
  | inr q =>
    exact and_congr (rescalePathTime_lt_iff hab _ t ht) (lt_rescalePathTime_iff hab _ t ht)

theorem affineRawTag_tuple_excluded_iff
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (a b : PathTime) (τ : TagSlot) :
    affineRawTag a b τ ∈ tagTupleExcluded N ↔ τ ∈ tagTupleExcluded N := by
  cases τ with
  | inl u => rfl
  | inr q =>
    exact (active_mem_tagTupleExcluded_iff N
      ⟨q.1, q.2.1, q.2.2.1, rescalePathTime a b q.2.2.2.1,
        rescalePathTime a b q.2.2.2.2⟩).trans (active_mem_tagTupleExcluded_iff N q).symm

variable {X : Type*} [MetricSpace X]

def affineRestrictedPath (a b : PathTime) (γ : C(PathTime, X)) : C(PathTime, X) :=
  γ.comp (affinePathTime a b)

def affineRestrictedTag (a b : PathTime) (γ : C(PathTime, X)) (τ : TagSlot) : TagSlot :=
  if (affineRestrictedPath a b γ, affineRawTag a b τ) ∈ nonconstantTagSegment
  then affineRawTag a b τ else inactiveTag

def affineRestrictedTaggedPath (a b : PathTime) (Γ : TaggedPath X) : TaggedPath X :=
  (affineRestrictedPath a b Γ.1, fun k => affineRestrictedTag a b Γ.1 (Γ.2 k))

omit [MetricSpace X] in
theorem affineRawTag_level_iff (H : ℕ → Set (UnitAddCircle × X))
    (a b : PathTime) (τ : TagSlot) (x : X) :
    (affineRawTag a b τ, x) ∈ tagLevelGraph H ↔ (τ, x) ∈ tagLevelGraph H := by
  cases τ <;> rfl

theorem affineRestrictedTag_rules (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    {a b : PathTime} (hab : a < b) (γ : C(PathTime, X)) (τ : TagSlot)
    (hc : (γ, τ) ∈ tagContainment H) (hn : τ ∉ tagTupleExcluded N) :
    (affineRestrictedPath a b γ, affineRestrictedTag a b γ τ) ∈ validTagShape ∧
      (affineRestrictedPath a b γ, affineRestrictedTag a b γ τ) ∈ tagContainment H ∧
      affineRestrictedTag a b γ τ ∉ tagTupleExcluded N := by
  by_cases h : (affineRestrictedPath a b γ, affineRawTag a b τ) ∈ nonconstantTagSegment
  · rw [affineRestrictedTag, ite_eq_left h]
    refine ⟨Or.inr h, ?_, fun hN => hn ((affineRawTag_tuple_excluded_iff N a b τ).mp hN)⟩
    intro t hl hr
    have ht : ⊥ < t ∧ t < ⊤ := ⟨lt_of_le_of_lt bot_le hl, lt_of_lt_of_le hr le_top⟩
    have hold := (affineRawTag_interval hab τ ht).mp ⟨hl, hr⟩
    exact (affineRawTag_level_iff H a b τ _).mpr (hc _ hold.1 hold.2)
  · rw [affineRestrictedTag, ite_eq_right h]
    exact inactiveTag_rules H N _

theorem tagRules_affineRestricted (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    {a b : PathTime} (hab : a < b) (Γ : TaggedPath X) (hΓ : TagRules H N Γ) :
    TagRules H N (affineRestrictedTaggedPath a b Γ) := by
  intro k
  exact affineRestrictedTag_rules H N hab Γ.1 (Γ.2 k) (hΓ k).2.1 (hΓ k).2.2

end CircleDomainRigidity

end

end OAI
