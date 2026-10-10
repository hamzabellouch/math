import OAI.Analysis.CircleDomains.Selection.TagDelay

namespace OAI

/-! Put countably many tag lists into one list without losing any tag.
Unused code slots are inactive, so tuple exclusions are preserved exactly. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

def assembleTags {ι : Type*} [Encodable ι] (θ : ι → ℕ → TagSlot) (k : ℕ) : TagSlot :=
  match Encodable.decode (α := ι × ℕ) k with
  | none => inactiveTag
  | some p => θ p.1 p.2

theorem assembleTags_at {ι : Type*} [Encodable ι] (θ : ι → ℕ → TagSlot) (i : ι) (k : ℕ) :
    assembleTags θ (Encodable.encode (i, k)) = θ i k := by
  simp only [assembleTags, Encodable.encodek]

theorem assembleTags_value {ι : Type*} [Encodable ι] (θ : ι → ℕ → TagSlot) (k : ℕ) :
    assembleTags θ k = inactiveTag ∨ ∃ i j, assembleTags θ k = θ i j := by
  unfold assembleTags
  cases Encodable.decode (α := ι × ℕ) k with
  | none => exact Or.inl rfl
  | some p => exact Or.inr ⟨p.1, p.2, rfl⟩

variable {X : Type*} [MetricSpace X]

theorem tagRules_assemble {ι : Type*} [Encodable ι]
    (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (θ : ι → ℕ → TagSlot)
    (hθ : ∀ i, TagRules H N (γ, θ i)) : TagRules H N (γ, assembleTags θ) := by
  intro k
  rcases assembleTags_value θ k with hk | ⟨i, j, hk⟩
  · change (γ, assembleTags θ k) ∈ validTagShape ∧
      (γ, assembleTags θ k) ∈ tagContainment H ∧ assembleTags θ k ∉ tagTupleExcluded N
    rw [hk]
    exact inactiveTag_rules H N γ
  · change (γ, assembleTags θ k) ∈ validTagShape ∧
      (γ, assembleTags θ k) ∈ tagContainment H ∧ assembleTags θ k ∉ tagTupleExcluded N
    rw [hk]
    exact hθ i j

theorem residualTimes_assemble_iff {ι : Type*} [Encodable ι]
    (B : Set X) (γ : C(PathTime, X)) (θ : ι → ℕ → TagSlot) (t : PathTime) :
    t ∈ residualTimes B (γ, assembleTags θ) ↔
      γ t ∈ B ∧ ∀ i j, t ≤ tagLeft (θ i j) ∨ tagRight (θ i j) ≤ t := by
  constructor
  · rintro ⟨ht, htags⟩
    refine ⟨ht, fun i j => ?_⟩
    simpa only [assembleTags_at] using htags (Encodable.encode (i, j))
  · rintro ⟨ht, htags⟩
    refine ⟨ht, fun k => ?_⟩
    rcases assembleTags_value θ k with hk | ⟨i, j, hk⟩
    · change t ≤ tagLeft (assembleTags θ k) ∨ tagRight (assembleTags θ k) ≤ t
      rw [hk]
      exact Or.inl le_top
    · change t ≤ tagLeft (assembleTags θ k) ∨ tagRight (assembleTags θ k) ≤ t
      rw [hk]
      exact htags i j

theorem residualTimes_assemble_on_piece {ι : Type*} [Encodable ι]
    (B : Set X) (γ : C(PathTime, X)) (θ : ι → ℕ → TagSlot)
    (J : ι → Set PathTime) (hJ : Pairwise (Disjoint on J))
    (hθ : ∀ i k, Ioo (tagLeft (θ i k)) (tagRight (θ i k)) ⊆ J i)
    (i : ι) {t : PathTime} (ht : t ∈ J i) :
    t ∈ residualTimes B (γ, assembleTags θ) ↔ t ∈ residualTimes B (γ, θ i) := by
  rw [residualTimes_assemble_iff]
  constructor
  · rintro ⟨hdust, htags⟩
    exact ⟨hdust, htags i⟩
  · rintro ⟨hdust, htags⟩
    refine ⟨hdust, fun j k => ?_⟩
    by_cases hij : j = i
    · subst j
      exact htags k
    · have hn : t ∉ Ioo (tagLeft (θ j k)) (tagRight (θ j k)) :=
        fun h => disjoint_left.mp (hJ hij) (hθ j k h) ht
      exact (not_and_or.mp hn).imp le_of_not_gt le_of_not_gt

end CircleDomainRigidity

end

end OAI
