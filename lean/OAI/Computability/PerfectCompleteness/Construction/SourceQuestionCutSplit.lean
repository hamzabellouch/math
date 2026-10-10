import OAI.Computability.PerfectCompleteness.Foundations.CutSlotOutside
import OAI.Computability.PerfectCompleteness.Sampling.PreliminarySampler

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionCutSplit

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t m : Nat}

abbrev OutsideLeaf (p : Path branch root h) :=
  {leaf : Slots branch root // leaf ∉ Set.range p.slotEmbedding}

abbrev OutsideQuestions (p : Path branch root h) (t m : Nat) :=
  OutsideLeaf p → Fin t → Fin m

def restrict (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m) :
    PreliminarySampler.Questions branch h t m :=
  fun leaf => q (p.slotEmbedding leaf)

def outside (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m) : OutsideQuestions p t m :=
  fun leaf => q leaf.val

def join (p : Path branch root h)
    (inside : PreliminarySampler.Questions branch h t m) (external : OutsideQuestions p t m) :
    PreliminarySampler.Questions branch root t m :=
  fun leaf => if hleaf : leaf ∈ Set.range p.slotEmbedding then
    inside (Classical.choose hleaf) else external ⟨leaf, hleaf⟩

@[simp] theorem join_at_cut (p : Path branch root h)
    (inside : PreliminarySampler.Questions branch h t m) (external : OutsideQuestions p t m)
    (leaf : Slots branch h) :
    join p inside external (p.slotEmbedding leaf) = inside leaf := by
  have hleaf : p.slotEmbedding leaf ∈ Set.range p.slotEmbedding := ⟨leaf, rfl⟩
  have hchoose : Classical.choose hleaf = leaf :=
    p.slotEmbedding_injective (Classical.choose_spec hleaf)
  simp only [join, dite_eq_left hleaf, hchoose]

@[simp] theorem join_outside (p : Path branch root h)
    (inside : PreliminarySampler.Questions branch h t m) (external : OutsideQuestions p t m)
    (leaf : OutsideLeaf p) :
    join p inside external leaf.val = external leaf := by
  simp only [join, dite_eq_right leaf.property]

theorem join_restrict (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m) :
    join p (restrict p q) (outside p q) = q := by
  funext leaf
  by_cases hleaf : leaf ∈ Set.range p.slotEmbedding
  · simp only [join, dite_eq_left hleaf, restrict, Classical.choose_spec hleaf]
  · simp only [join, dite_eq_right hleaf, outside]

def splitEquiv (p : Path branch root h) :
    PreliminarySampler.Questions branch root t m ≃
      PreliminarySampler.Questions branch h t m × OutsideQuestions p t m where
  toFun q := (restrict p q, outside p q)
  invFun parts := join p parts.1 parts.2
  left_inv q := join_restrict p q
  right_inv parts := by
    apply Prod.ext
    · funext leaf
      exact join_at_cut p parts.1 parts.2 leaf
    · funext leaf
      exact join_outside p parts.1 parts.2 leaf

@[simp] theorem splitEquiv_apply (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m) :
    splitEquiv p q = (restrict p q, outside p q) := rfl

@[simp] theorem splitEquiv_symm_apply (p : Path branch root h)
    (inside : PreliminarySampler.Questions branch h t m) (external : OutsideQuestions p t m) :
    (splitEquiv p).symm (inside, external) = join p inside external := rfl

theorem split_law [NeZero m] (p : Path branch root h) :
    (PreliminarySampler.questionsLaw (branch := branch) (n := root) (t := t) (m := m)).pushforward
        (splitEquiv p) =
      (PreliminarySampler.questionsLaw (branch := branch) (n := h) (t := t) (m := m)).product
        (FiniteDistribution.uniform (OutsideQuestions p t m)) := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro pair
  change 1 / (Fintype.card (PreliminarySampler.Questions branch root t m) : ℝ) =
    (1 / (Fintype.card (PreliminarySampler.Questions branch h t m) : ℝ)) *
      (1 / (Fintype.card (OutsideQuestions p t m) : ℝ))
  rw [Fintype.card_congr (splitEquiv (t := t) (m := m) p), Fintype.card_prod,
    Nat.cast_mul, one_div_mul_one_div]

theorem join_eq_fill (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m)
    (inside : PreliminarySampler.Questions branch h t m) :
    join p inside (outside p q) = CutSlotAssembly.fill p q inside := by
  funext leaf
  by_cases hleaf : leaf ∈ Set.range p.slotEmbedding
  · obtain ⟨s, rfl⟩ := hleaf
    exact (join_at_cut p inside (outside p q) s).trans
      (CutSlotAssembly.fill_at_cut p q inside s).symm
  · exact (join_outside p inside (outside p q) ⟨leaf, hleaf⟩).trans
      (CutSlotAssembly.fill_outside p q inside leaf hleaf).symm

variable {v : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)

theorem sourceSlots_restrict (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m) :
    HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints (restrict p q)) =
      fun leaf j => HierarchicalArrays.sourceSlots clauses
        (PreliminarySampler.endpoints q) (p.slotEmbedding leaf) j := rfl

theorem sourceSlots_fill (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m)
    (inside : PreliminarySampler.Questions branch h t m) :
    HierarchicalArrays.sourceSlots clauses
        (PreliminarySampler.endpoints (CutSlotAssembly.fill p q inside)) =
      CutSlotAssembly.fill p
        (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q))
        (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints inside)) := by
  funext leaf j
  by_cases hleaf : leaf ∈ Set.range p.slotEmbedding
  · obtain ⟨s, rfl⟩ := hleaf
    exact (congrArg (fun row : Fin t → Fin m => SourceKeys.slot clauses (.clause (row j)))
      (CutSlotAssembly.fill_at_cut p q inside s)).trans
      (congrFun (CutSlotAssembly.fill_at_cut p
        (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q))
        (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints inside)) s) j).symm
  · exact (congrArg (fun row : Fin t → Fin m => SourceKeys.slot clauses (.clause (row j)))
      (CutSlotAssembly.fill_outside p q inside leaf hleaf)).trans
      (congrFun (CutSlotAssembly.fill_outside p
        (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q))
        (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints inside)) leaf hleaf) j).symm

theorem sourceSlots_join (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m)
    (inside : PreliminarySampler.Questions branch h t m) :
    HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints (join p inside (outside p q))) =
      CutSlotAssembly.fill p
        (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q))
        (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints inside)) := by
  rw [join_eq_fill]
  exact sourceSlots_fill clauses p q inside

end
end PerfectCompleteness.SourceQuestionCutSplit

end

end OAI
