import OAI.Combinatorics.GraphThreshold.ProbabilityTree
import Mathlib.Tactic

namespace OAI

/-! Path and locality facts for the stable finite probability-tree representation. -/

noncomputable section

namespace LeanBlast.SecondKahnKalai

section Locality

variable {X β : Type*} [DecidableEq X] {S T A : Finset X} {f : Finset X → β}

theorem DependsOnlyOn.mono (hf : DependsOnlyOn S f) (hST : S ⊆ T) :
    DependsOnlyOn T f := by
  intro W V hWV
  apply hf W V
  apply Finset.ext
  intro x
  by_cases hx : x ∈ S
  · have hxT := hST hx
    have he := Finset.ext_iff.mp hWV x
    simpa [hx, hxT] using he
  · simp [hx]

theorem DependsOnlyOn.dependsOutside (hf : DependsOnlyOn S f) (hAS : Disjoint A S) :
    DependsOutside A f := by
  intro W V hWV
  apply hf W V
  apply Finset.ext
  intro x
  by_cases hx : x ∈ S
  · have hxA : x ∉ A := fun hxA => Finset.disjoint_left.mp hAS hxA hx
    have he := Finset.ext_iff.mp hWV x
    simpa [hx, hxA] using he
  · simp [hx]

theorem DependsOutside.sdiff_eq (hf : DependsOutside A f) (W : Finset X) :
    f (W \ A) = f W := by
  apply hf
  ext x
  simp

theorem dependsOutside_iff_sdiff :
    DependsOutside A f ↔ ∀ W, f (W \ A) = f W := by
  constructor
  · exact fun hf => hf.sdiff_eq
  · intro hf W V hWV
    rw [← hf W, ← hf V, hWV]

theorem DependsOutside.union_eq (hf : DependsOutside A f) (W U : Finset X) (hU : U ⊆ A) :
    f (W ∪ U) = f W := by
  apply hf
  ext x
  by_cases hx : x ∈ A
  · simp [hx]
  · have hxU : x ∉ U := fun hxU => hx (hU hxU)
    simp [hx, hxU]

end Locality

namespace ProbabilityTree

variable {X : Type}

/-- A finite law of total mass one has a nonempty underlying type. -/
theorem branch_nonempty {B : Type} [Fintype B] (law : FiniteLaw B) : Nonempty B := by
  classical
  by_contra h
  let : IsEmpty B := not_nonempty_iff.mp h
  have ht := law.total
  simp at ht

/-- Every equal-depth probability tree has at least one full path. -/
instance pathNonempty {d : ℕ} (T : ProbabilityTree X d) : Nonempty T.Path := by
  induction T with
  | leaf => exact ⟨PUnit.unit⟩
  | @node d B inst law positive label child ih =>
      let b : B := Classical.choice (branch_nonempty law)
      exact ⟨⟨b, Classical.choice (ih b)⟩⟩

/-- A fixed deterministic full path, used only to resolve finite choices. -/
def choosePath {d : ℕ} (T : ProbabilityTree X d) : T.Path := Classical.choice (pathNonempty T)

@[simp] theorem pathLabels_length {d : ℕ} (T : ProbabilityTree X d) (p : T.Path) :
    (T.pathLabels p).length = d := by
  induction T with
  | leaf => rfl
  | @node d B inst law positive label child ih =>
      rcases p with ⟨b, p⟩
      simpa [pathLabels] using congrArg Nat.succ (ih b p)

section Labels

variable [DecidableEq X]

theorem label_subset_support {d : ℕ} {B : Type} [Fintype B]
    (law : FiniteLaw B) (positive : law.IsPositive) (label : B → Finset X)
    (child : B → ProbabilityTree X d) (b : B) :
    label b ⊆ (node B law positive label child).support := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, Finset.mem_union_left _ hx⟩

theorem child_support_subset {d : ℕ} {B : Type} [Fintype B]
    (law : FiniteLaw B) (positive : law.IsPositive) (label : B → Finset X)
    (child : B → ProbabilityTree X d) (b : B) :
    (child b).support ⊆ (node B law positive label child).support := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, Finset.mem_union_right _ hx⟩

theorem labels_support_subset {d : ℕ} {B : Type} [Fintype B]
    (law : FiniteLaw B) (positive : law.IsPositive) (label : B → Finset X)
    (child : B → ProbabilityTree X d) :
    (Finset.univ.biUnion label) ⊆ (node B law positive label child).support := by
  intro x hx
  obtain ⟨b, _, hxb⟩ := Finset.mem_biUnion.mp hx
  exact label_subset_support law positive label child b hxb

theorem child_dependsOutside {d : ℕ} {B : Type} [Fintype B]
    {law : FiniteLaw B} {positive : law.IsPositive} {label : B → Finset X}
    {child : B → ProbabilityTree X d}
    (hT : (node B law positive label child).IsDisjoint) (b : B)
    {β : Type*} {f : Finset X → β} (hf : DependsOnlyOn (child b).support f) :
    DependsOutside (label b) f :=
  hf.dependsOutside (hT.1 b)

end Labels

end ProbabilityTree

end LeanBlast.SecondKahnKalai

end

end OAI
