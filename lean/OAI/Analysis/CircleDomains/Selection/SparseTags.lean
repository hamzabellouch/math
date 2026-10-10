import OAI.Analysis.CircleDomains.Selection.TagDelay

namespace OAI

/-! Arbitrary injective reassignment of tag slots. All geometric data and
residual conditions are preserved, including unused slots. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

def sparseTags (e : ℕ ↪ ℕ) (θ : ℕ → TagSlot) (k : ℕ) : TagSlot :=
  if h : ∃ i, e i = k then θ h.choose else inactiveTag

theorem sparseTags_at (e : ℕ ↪ ℕ) (θ : ℕ → TagSlot) (i : ℕ) :
    sparseTags e θ (e i) = θ i := by
  have h : ∃ j, e j = e i := ⟨i, rfl⟩
  have hi : h.choose = i := e.injective h.choose_spec
  simp only [sparseTags, dite_eq_left h, hi]

theorem sparseTags_outside (e : ℕ ↪ ℕ) (θ : ℕ → TagSlot) {k : ℕ}
    (hk : k ∉ Set.range e) : sparseTags e θ k = inactiveTag := by
  exact dite_eq_right hk

theorem continuous_sparseTags (e : ℕ ↪ ℕ) : Continuous (sparseTags e) := by
  apply continuous_pi
  intro k
  by_cases h : ∃ i, e i = k
  · simpa only [sparseTags, dite_eq_left h] using
      (continuous_apply h.choose : Continuous (fun θ : ℕ → TagSlot => θ h.choose))
  · simpa only [sparseTags, dite_eq_right h] using
      (continuous_const : Continuous (fun _ : ℕ → TagSlot => inactiveTag))

def sparseTaggedPath {X : Type*} [TopologicalSpace X] (e : ℕ ↪ ℕ)
    (Γ : TaggedPath X) : TaggedPath X := (Γ.1, sparseTags e Γ.2)

theorem continuous_sparseTaggedPath {X : Type*} [TopologicalSpace X] (e : ℕ ↪ ℕ) :
    Continuous (sparseTaggedPath (X := X) e) :=
  continuous_fst.prodMk ((continuous_sparseTags e).comp continuous_snd)

theorem residualTimes_sparse {X : Type*} [TopologicalSpace X]
    (B : Set X) (e : ℕ ↪ ℕ) (Γ : TaggedPath X) :
    residualTimes B (sparseTaggedPath e Γ) = residualTimes B Γ := by
  ext t
  constructor
  · rintro ⟨ht, htags⟩
    refine ⟨ht, fun i => ?_⟩
    simpa only [sparseTaggedPath, sparseTags_at] using htags (e i)
  · rintro ⟨ht, htags⟩
    refine ⟨ht, fun k => ?_⟩
    by_cases hk : k ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hk
      simpa only [sparseTaggedPath, sparseTags_at] using htags i
    · left
      simp only [sparseTaggedPath, sparseTags_outside e Γ.2 hk, inactiveTag,
        tagLeft, Sum.elim_inl]
      exact le_top

theorem residualImage_sparse {X : Type*} [MetricSpace X]
    (B : Set X) (e : ℕ ↪ ℕ) (Γ : TaggedPath X) :
    residualImage B (sparseTaggedPath e Γ) = residualImage B Γ := by
  rw [residualImage, residualTimes_sparse]
  rfl

variable {X : Type*} [MetricSpace X]

theorem tagRules_sparse (H : ℕ → Set (UnitAddCircle × X))
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (e : ℕ ↪ ℕ) {Γ : TaggedPath X} (hΓ : TagRules H T Γ) :
    TagRules H T (sparseTaggedPath e Γ) := by
  intro k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    simpa only [sparseTaggedPath, sparseTags_at] using hΓ i
  · simpa only [sparseTaggedPath, sparseTags_outside e Γ.2 hk] using
      inactiveTag_rules H T Γ.1

theorem residualIncidence_sparse {Z : Type*} (B : Set X) (I : Set PathTime)
    (R : Set (Z × X)) (P : Set X) (e : ℕ ↪ ℕ) (Γ : TaggedPath X) (z : Z) :
    (sparseTaggedPath e Γ, z) ∈ residualIncidence B I R P ↔
      (Γ, z) ∈ residualIncidence B I R P := by
  change (∃ t ∈ residualTimes B (sparseTaggedPath e Γ),
    t ∈ I ∧ (z, Γ.1 t) ∈ R ∧ Γ.1 t ∉ P) ↔ _
  rw [residualTimes_sparse]
  rfl

theorem residualToll_sparse (B : Set X) (I : Set PathTime) (m : X → ℝ≥0∞)
    (e : ℕ ↪ ℕ) (Γ : TaggedPath X) :
    residualToll B I m (sparseTaggedPath e Γ) = residualToll B I m Γ := by
  unfold residualToll
  rw [residualTimes_sparse]
  rfl

theorem residualConstraintFamily_sparse {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (e : ℕ ↪ ℕ) (Γ : TaggedPath X) :
    ResidualConstraintFamily B R P ν m (sparseTaggedPath e Γ) ↔
      ResidualConstraintFamily B R P ν m Γ := by
  unfold ResidualConstraintFamily ResidualIncidenceBound
  simp only [residualIncidence_sparse, residualToll_sparse]

end CircleDomainRigidity

end

end OAI
