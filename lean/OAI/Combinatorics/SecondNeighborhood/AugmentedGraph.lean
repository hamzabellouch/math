import OAI.Combinatorics.SecondNeighborhood.PruningDefinitions
import OAI.Combinatorics.SecondNeighborhood.Matching
import Mathlib.Data.Fintype.Sum

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev LeftVertex (r : V → V → Prop) (R C : Finset (V × V)) :=
  ↥R ⊕ ↥(Z r R C)

abbrev RightVertex (r : V → V → Prop) (R C : Finset (V × V)) :=
  ↥C ⊕ ↥(Z r R C)

def AugmentedEdge (r : V → V → Prop) (R C : Finset (V × V)) :
    LeftVertex r R C → RightVertex r R C → Prop
  | Sum.inl a, Sum.inl b => Conflict r a.val b.val
  | Sum.inl a, Sum.inr z => LeftCovers r a.val z.val
  | Sum.inr z, Sum.inl b => RightCovers r b.val z.val
  | Sum.inr _, Sum.inr _ => False

def OriginalRelation (r : V → V → Prop) (R C : Finset (V × V))
    (a : R) (b : C) : Prop := Conflict r a.val b.val

def AlphaRelation (r : V → V → Prop) (R C : Finset (V × V))
    (z : Z r R C) (a : R) : Prop := LeftCovers r a.val z.val

def BetaRelation (r : V → V → Prop) (R C : Finset (V × V))
    (z : Z r R C) (b : C) : Prop := RightCovers r b.val z.val

variable {r : V → V → Prop} {R C : Finset (V × V)}

def originalLift (e : ↥R × ↥C) : LeftVertex r R C × RightVertex r R C :=
  (Sum.inl e.1, Sum.inl e.2)

def alphaLift (e : ↥(Z r R C) × ↥R) :
    LeftVertex r R C × RightVertex r R C :=
  (Sum.inl e.2, Sum.inr e.1)

def betaLift (e : ↥(Z r R C) × ↥C) :
    LeftVertex r R C × RightVertex r R C :=
  (Sum.inr e.1, Sum.inl e.2)

theorem originalLift_injective :
    Function.Injective (originalLift (r := r) (R := R) (C := C)) := by
  intro e f h
  exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h))
    (Sum.inl.inj (congrArg Prod.snd h))

theorem alphaLift_injective :
    Function.Injective (alphaLift (r := r) (R := R) (C := C)) := by
  intro e f h
  exact Prod.ext (Sum.inr.inj (congrArg Prod.snd h))
    (Sum.inl.inj (congrArg Prod.fst h))

theorem betaLift_injective :
    Function.Injective (betaLift (r := r) (R := R) (C := C)) := by
  intro e f h
  exact Prod.ext (Sum.inr.inj (congrArg Prod.fst h))
    (Sum.inl.inj (congrArg Prod.snd h))

noncomputable def originalEdges
    (M : Finset (LeftVertex r R C × RightVertex r R C)) : Finset (↥R × ↥C) := by
  classical
  exact Finset.univ.filter (fun e => originalLift e ∈ M)

noncomputable def alphaEdges
    (M : Finset (LeftVertex r R C × RightVertex r R C)) :
    Finset (↥(Z r R C) × ↥R) := by
  classical
  exact Finset.univ.filter (fun e => alphaLift e ∈ M)

noncomputable def betaEdges
    (M : Finset (LeftVertex r R C × RightVertex r R C)) :
    Finset (↥(Z r R C) × ↥C) := by
  classical
  exact Finset.univ.filter (fun e => betaLift e ∈ M)

@[simp] theorem mem_originalEdges
    {M : Finset (LeftVertex r R C × RightVertex r R C)} {e : ↥R × ↥C} :
    e ∈ originalEdges M ↔ originalLift e ∈ M := by
  classical
  simp [originalEdges]

@[simp] theorem mem_alphaEdges
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    {e : ↥(Z r R C) × ↥R} : e ∈ alphaEdges M ↔ alphaLift e ∈ M := by
  classical
  simp [alphaEdges]

@[simp] theorem mem_betaEdges
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    {e : ↥(Z r R C) × ↥C} : e ∈ betaEdges M ↔ betaLift e ∈ M := by
  classical
  simp [betaEdges]

theorem originalEdges_isMatching
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    IsMatching (OriginalRelation r R C) (originalEdges M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact hM.1 (originalLift e) (mem_originalEdges.mp he)
  · intro e he f hf h
    apply originalLift_injective
    exact hM.2.1 (mem_originalEdges.mp he) (mem_originalEdges.mp hf)
      (congrArg Sum.inl h)
  · intro e he f hf h
    apply originalLift_injective
    exact hM.2.2 (mem_originalEdges.mp he) (mem_originalEdges.mp hf)
      (congrArg Sum.inl h)

theorem alphaEdges_isMatching
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    IsMatching (AlphaRelation r R C) (alphaEdges M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact hM.1 (alphaLift e) (mem_alphaEdges.mp he)
  · intro e he f hf h
    apply alphaLift_injective
    exact hM.2.2 (mem_alphaEdges.mp he) (mem_alphaEdges.mp hf)
      (congrArg Sum.inr h)
  · intro e he f hf h
    apply alphaLift_injective
    exact hM.2.1 (mem_alphaEdges.mp he) (mem_alphaEdges.mp hf)
      (congrArg Sum.inl h)

theorem betaEdges_isMatching
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    IsMatching (BetaRelation r R C) (betaEdges M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact hM.1 (betaLift e) (mem_betaEdges.mp he)
  · intro e he f hf h
    apply betaLift_injective
    exact hM.2.1 (mem_betaEdges.mp he) (mem_betaEdges.mp hf)
      (congrArg Sum.inr h)
  · intro e he f hf h
    apply betaLift_injective
    exact hM.2.2 (mem_betaEdges.mp he) (mem_betaEdges.mp hf)
      (congrArg Sum.inl h)

theorem original_alpha_left_ne
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M)
    {e : ↥R × ↥C} (he : e ∈ originalEdges M)
    {a : ↥(Z r R C) × ↥R} (ha : a ∈ alphaEdges M) : e.1 ≠ a.2 := by
  intro h
  have heq := hM.2.1 (mem_originalEdges.mp he) (mem_alphaEdges.mp ha)
    (congrArg Sum.inl h)
  have hright := congrArg Prod.snd heq
  cases hright

theorem original_beta_right_ne
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M)
    {e : ↥R × ↥C} (he : e ∈ originalEdges M)
    {b : ↥(Z r R C) × ↥C} (hb : b ∈ betaEdges M) : e.2 ≠ b.2 := by
  intro h
  have heq := hM.2.2 (mem_originalEdges.mp he) (mem_betaEdges.mp hb)
    (congrArg Sum.inl h)
  have hleft := congrArg Prod.fst heq
  cases hleft

theorem alphaEdges_image
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    (alphaEdges M).image alphaLift = M.filter (fun e => e.2.isRight) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨⟨z, a⟩, ha, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨mem_alphaEdges.mp ha, rfl⟩
  · intro he
    obtain ⟨he, hright⟩ := Finset.mem_filter.mp he
    obtain ⟨l, b⟩ := e
    cases l with
    | inl a =>
      cases b with
      | inl b => simp at hright
      | inr z => exact Finset.mem_image.mpr ⟨(z, a), mem_alphaEdges.mpr he, rfl⟩
    | inr z =>
      cases b with
      | inl b => simp at hright
      | inr w => exact False.elim (hM.1 _ he)

theorem betaEdges_image
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    (betaEdges M).image betaLift = M.filter (fun e => e.1.isRight) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨⟨z, b⟩, hb, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨mem_betaEdges.mp hb, rfl⟩
  · intro he
    obtain ⟨he, hleft⟩ := Finset.mem_filter.mp he
    obtain ⟨l, b⟩ := e
    cases l with
    | inl a => simp at hleft
    | inr z =>
      cases b with
      | inl b => exact Finset.mem_image.mpr ⟨(z, b), mem_betaEdges.mpr he, rfl⟩
      | inr w => exact False.elim (hM.1 _ he)

theorem augmented_matching_eq_three_images
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    M = (originalEdges M).image originalLift ∪
      (alphaEdges M).image alphaLift ∪ (betaEdges M).image betaLift := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨l, b⟩ := e
    cases l with
    | inl a =>
      cases b with
      | inl b =>
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨(a, b), mem_originalEdges.mpr he, rfl⟩))
      | inr z =>
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(z, a), mem_alphaEdges.mpr he, rfl⟩))
    | inr z =>
      cases b with
      | inl b =>
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(z, b), mem_betaEdges.mpr he, rfl⟩)
      | inr w => exact False.elim (hM.1 _ he)
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_union.mp he with he | he
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
        exact mem_originalEdges.mp ha
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
        exact mem_alphaEdges.mp ha
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact mem_betaEdges.mp ha

theorem augmented_matching_card
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M) :
    M.card = (originalEdges M).card + (alphaEdges M).card + (betaEdges M).card := by
  classical
  have hOA : Disjoint ((originalEdges M).image originalLift)
      ((alphaEdges M).image alphaLift) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨a, _, h⟩ := Finset.mem_image.mp hf
    have hright := congrArg Prod.snd h
    cases hright
  have hOB : Disjoint ((originalEdges M).image originalLift)
      ((betaEdges M).image betaLift) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, h⟩ := Finset.mem_image.mp hf
    have hleft := congrArg Prod.fst h
    cases hleft
  have hAB : Disjoint ((alphaEdges M).image alphaLift)
      ((betaEdges M).image betaLift) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, h⟩ := Finset.mem_image.mp hf
    have hleft := congrArg Prod.fst h
    cases hleft
  calc
    M.card = (((originalEdges M).image originalLift ∪
        (alphaEdges M).image alphaLift) ∪ (betaEdges M).image betaLift).card :=
      congrArg Finset.card (augmented_matching_eq_three_images hM)
    _ = _ := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hOB, hAB⟩),
        Finset.card_union_of_disjoint hOA,
        Finset.card_image_of_injective _ originalLift_injective,
        Finset.card_image_of_injective _ alphaLift_injective,
        Finset.card_image_of_injective _ betaLift_injective]

end SeymourSecondNeighborhood.Pruning

end OAI
