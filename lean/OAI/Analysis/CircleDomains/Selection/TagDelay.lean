import OAI.Analysis.CircleDomains.Topology.BasePathCodes
import OAI.Analysis.CircleDomains.Probability.TagTupleMeasure

namespace OAI

/-! Moving the same tags to later slots preserves the actual residual times
and all admissibility rules. The tuple measure decreases geometrically. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

def inactiveTag : TagSlot := Sum.inl ()

def delayTags (N : ℕ) (θ : ℕ → TagSlot) (k : ℕ) : TagSlot :=
  if k < N then inactiveTag else θ (k - N)

theorem delayTags_before (N : ℕ) (θ : ℕ → TagSlot) {k : ℕ} (hk : k < N) :
    delayTags N θ k = inactiveTag := by simp only [delayTags, hk, ite_true]

theorem delayTags_add (N : ℕ) (θ : ℕ → TagSlot) (k : ℕ) :
    delayTags N θ (N + k) = θ k := by
  simp only [delayTags, Nat.not_lt.mpr (Nat.le_add_right N k), ite_false, Nat.add_sub_cancel_left]

theorem continuous_delayTags (N : ℕ) : Continuous (delayTags N) := by
  apply continuous_pi
  intro k
  by_cases hk : k < N
  · simpa only [delayTags, hk, ite_true] using
      (continuous_const : Continuous (fun _ : ℕ → TagSlot => inactiveTag))
  · simpa only [delayTags, hk, ite_false] using
      (continuous_apply (k - N) : Continuous (fun θ : ℕ → TagSlot => θ (k - N)))

def delayTaggedPath {X : Type*} [TopologicalSpace X] (N : ℕ) (Γ : TaggedPath X) : TaggedPath X :=
  (Γ.1, delayTags N Γ.2)

theorem continuous_delayTaggedPath {X : Type*} [TopologicalSpace X] (N : ℕ) :
    Continuous (delayTaggedPath (X := X) N) :=
  continuous_fst.prodMk ((continuous_delayTags N).comp continuous_snd)

theorem residualTimes_delay {X : Type*} [TopologicalSpace X]
    (B : Set X) (N : ℕ) (Γ : TaggedPath X) :
    residualTimes B (delayTaggedPath N Γ) = residualTimes B Γ := by
  ext t
  constructor
  · rintro ⟨ht, htags⟩
    refine ⟨ht, fun k => ?_⟩
    have h := htags (N + k)
    simpa only [delayTaggedPath, delayTags_add] using h
  · rintro ⟨ht, htags⟩
    refine ⟨ht, fun k => ?_⟩
    by_cases hk : k < N
    · left
      simp only [delayTaggedPath, delayTags_before N Γ.2 hk, inactiveTag, tagLeft, Sum.elim_inl]
      exact le_top
    · simpa only [delayTaggedPath, delayTags, hk, ite_false] using htags (k - N)

theorem residualImage_delay {X : Type*} [MetricSpace X]
    (B : Set X) (N : ℕ) (Γ : TaggedPath X) :
    residualImage B (delayTaggedPath N Γ) = residualImage B Γ := by
  rw [residualImage, residualTimes_delay]
  rfl

variable {X : Type*} [MetricSpace X]

theorem inactiveTag_rules (H : ℕ → Set (UnitAddCircle × X))
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) :
    (γ, inactiveTag) ∈ validTagShape ∧ (γ, inactiveTag) ∈ tagContainment H ∧
      inactiveTag ∉ tagTupleExcluded T := by
  refine ⟨Or.inl ⟨(), rfl⟩, ?_, ?_⟩
  · intro t hleft _
    exact False.elim (not_lt_of_ge le_top hleft)
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    obtain ⟨l, hl⟩ := mem_iUnion.mp hn
    obtain ⟨p, _, heq⟩ := hl
    cases heq

theorem tagRules_delay (H : ℕ → Set (UnitAddCircle × X))
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (N : ℕ) {Γ : TaggedPath X} (hΓ : TagRules H T Γ) :
    TagRules H T (delayTaggedPath N Γ) := by
  intro k
  by_cases hk : k < N
  · simpa only [delayTaggedPath, delayTags_before N Γ.2 hk] using inactiveTag_rules H T Γ.1
  · simpa only [delayTaggedPath, delayTags, hk, ite_false] using hΓ (k - N)

theorem residualIncidence_delay {Z : Type*} (B : Set X) (I : Set PathTime)
    (R : Set (Z × X)) (P : Set X) (N : ℕ) (Γ : TaggedPath X) (z : Z) :
    (delayTaggedPath N Γ, z) ∈ residualIncidence B I R P ↔
      (Γ, z) ∈ residualIncidence B I R P := by
  change (∃ t ∈ residualTimes B (delayTaggedPath N Γ),
    t ∈ I ∧ (z, Γ.1 t) ∈ R ∧ Γ.1 t ∉ P) ↔ _
  rw [residualTimes_delay]
  rfl

theorem residualToll_delay (B : Set X) (I : Set PathTime) (m : X → ℝ≥0∞)
    (N : ℕ) (Γ : TaggedPath X) :
    residualToll B I m (delayTaggedPath N Γ) = residualToll B I m Γ := by
  unfold residualToll
  rw [residualTimes_delay]
  rfl

theorem residualConstraintFamily_delay {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (N : ℕ) (Γ : TaggedPath X) :
    ResidualConstraintFamily B R P ν m (delayTaggedPath N Γ) ↔
      ResidualConstraintFamily B R P ν m Γ := by
  unfold ResidualConstraintFamily ResidualIncidenceBound
  simp only [residualIncidence_delay, residualToll_delay]

end CircleDomainRigidity

end

end OAI
