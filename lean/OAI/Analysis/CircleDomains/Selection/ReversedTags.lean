import OAI.Analysis.CircleDomains.Selection.NarrowedTagRules

namespace OAI

/-! Reversal of a tagged path retains every level tuple and reverses its
open time interval. Residual times and images are transported exactly. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

def reversedTag : TagSlot → TagSlot
  | Sum.inl u => Sum.inl u
  | Sum.inr q => Sum.inr ⟨q.1, q.2.1, q.2.2.1,
      unitInterval.symm q.2.2.2.2, unitInterval.symm q.2.2.2.1⟩

theorem tagLeft_reversed (τ : TagSlot) :
    tagLeft (reversedTag τ) = unitInterval.symm (tagRight τ) := by
  cases τ with
  | inl u =>
    apply Subtype.ext
    change (1 : ℝ) = 1 - 0
    norm_num
  | inr q => rfl

theorem tagRight_reversed (τ : TagSlot) :
    tagRight (reversedTag τ) = unitInterval.symm (tagLeft τ) := by
  cases τ with
  | inl u =>
    apply Subtype.ext
    change (0 : ℝ) = 1 - 1
    norm_num
  | inr q => rfl

theorem reversedTag_tuple_excluded_iff
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (τ : TagSlot) : reversedTag τ ∈ tagTupleExcluded N ↔ τ ∈ tagTupleExcluded N := by
  cases τ with
  | inl u => rfl
  | inr q =>
    exact (active_mem_tagTupleExcluded_iff N
      ⟨q.1, q.2.1, q.2.2.1, unitInterval.symm q.2.2.2.2,
        unitInterval.symm q.2.2.2.1⟩).trans (active_mem_tagTupleExcluded_iff N q).symm

variable {X : Type*} [MetricSpace X]

def reversedPath (γ : C(PathTime, X)) : C(PathTime, X) :=
  γ.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩

def reversedTaggedPath (Γ : TaggedPath X) : TaggedPath X :=
  (reversedPath Γ.1, fun k => reversedTag (Γ.2 k))

omit [MetricSpace X] in
theorem reversedTag_level_iff (H : ℕ → Set (UnitAddCircle × X)) (τ : TagSlot) (x : X) :
    (reversedTag τ, x) ∈ tagLevelGraph H ↔ (τ, x) ∈ tagLevelGraph H := by
  cases τ <;> rfl

theorem tagRules_reversed (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) (hΓ : TagRules H N Γ) : TagRules H N (reversedTaggedPath Γ) := by
  intro k
  refine ⟨?_, ?_, fun hn => (hΓ k).2.2 ((reversedTag_tuple_excluded_iff N (Γ.2 k)).mp hn)⟩
  · rcases (hΓ k).1 with hinactive | hnonconstant
    · obtain ⟨u, hu⟩ := hinactive
      change (Sum.inl u : TagSlot) = Γ.2 k at hu
      change (reversedPath Γ.1, reversedTag (Γ.2 k)) ∈ validTagShape
      rw [← hu]
      exact Or.inl ⟨u, rfl⟩
    · obtain ⟨s, t, hsl, hsr, htl, htr, hne⟩ := hnonconstant
      refine Or.inr ⟨unitInterval.symm s, unitInterval.symm t, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [reversedTaggedPath, tagLeft_reversed, unitInterval.symm_lt_symm] using hsr
      · simpa only [reversedTaggedPath, tagRight_reversed, unitInterval.symm_lt_symm] using hsl
      · simpa only [reversedTaggedPath, tagLeft_reversed, unitInterval.symm_lt_symm] using htr
      · simpa only [reversedTaggedPath, tagRight_reversed, unitInterval.symm_lt_symm] using htl
      · simpa only [reversedTaggedPath, reversedPath, ContinuousMap.comp_apply,
          ContinuousMap.coe_mk, unitInterval.symm_symm] using hne
  · intro t hl hr
    change tagLeft (reversedTag (Γ.2 k)) < t at hl
    change t < tagRight (reversedTag (Γ.2 k)) at hr
    rw [tagLeft_reversed, unitInterval.symm_lt_comm] at hl
    rw [tagRight_reversed, unitInterval.lt_symm_comm] at hr
    exact (reversedTag_level_iff H (Γ.2 k) _).mpr ((hΓ k).2.1 _ hr hl)

theorem residualTimes_reversed (B : Set X) (Γ : TaggedPath X) :
    residualTimes B (reversedTaggedPath Γ) = unitInterval.symm ⁻¹' residualTimes B Γ := by
  ext t
  change (Γ.1 (unitInterval.symm t) ∈ B ∧ ∀ k,
    t ≤ tagLeft (reversedTag (Γ.2 k)) ∨ tagRight (reversedTag (Γ.2 k)) ≤ t) ↔
    (Γ.1 (unitInterval.symm t) ∈ B ∧ ∀ k,
      unitInterval.symm t ≤ tagLeft (Γ.2 k) ∨ tagRight (Γ.2 k) ≤ unitInterval.symm t)
  simp only [tagLeft_reversed, tagRight_reversed, unitInterval.le_symm_comm,
    unitInterval.symm_le_comm, or_comm]

theorem residualImage_reversed (B : Set X) (Γ : TaggedPath X) :
    residualImage B (reversedTaggedPath Γ) = residualImage B Γ := by
  rw [residualImage, residualTimes_reversed]
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨unitInterval.symm t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    refine ⟨unitInterval.symm t, ?_, ?_⟩
    · simpa only [mem_preimage, unitInterval.symm_symm] using ht
    · simpa only [reversedTaggedPath, reversedPath, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, unitInterval.symm_symm] using hx

end CircleDomainRigidity

end

end OAI
