import OAI.Computability.PerfectCompleteness.Sampling.SourceChildQuestionLaw

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPositionSplit

noncomputable section

open scoped Classical
open RecursiveSpaces SourceQuestionReconstruction TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t m : Nat}

abbrev Questions := PreliminarySampler.Questions branch (n + 1) t m
abbrev Positions := Slots branch (n + 1) → Fin t → Fin 3
abbrev ChildPositions := Slots branch n → Fin t → Fin 3

def splitTree : (Slots branch (n + 1) → SourceTuple m t) ≃
    Questions (branch := branch) (n := n) (t := t) (m := m) ×
      Positions (branch := branch) (n := n) (t := t) where
  toFun tree := (fun leaf k => (tree leaf k).1, fun leaf k => (tree leaf k).2)
  invFun parts leaf k := (parts.1 leaf k, parts.2 leaf k)
  left_inv _ := rfl
  right_inv _ := rfl

def split (designated : Fin (branch n) → Slots branch n) :
    SourceChildKernel.Sources (m := m) (t := t) designated ≃
      Questions (branch := branch) (n := n) (t := t) (m := m) ×
        Positions (branch := branch) (n := n) (t := t) :=
  (SourceChildQuestionLaw.assembleEquiv (m := m) (t := t) designated).trans splitTree

def join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    SourceChildKernel.Sources (m := m) (t := t) designated :=
  (split designated).symm (q, positions)

@[simp] theorem questions_join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    SourceChildQuestionLaw.questions designated (join designated q positions) = q :=
  congrArg Prod.fst ((split designated).apply_symm_apply (q, positions))

theorem tree_join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    SourceChildQuestionLaw.assembleEquiv designated (join designated q positions) =
      fun leaf k => (q leaf k, positions leaf k) :=
  (SourceChildQuestionLaw.assembleEquiv (m := m) (t := t) designated).apply_symm_apply _

theorem child_tree_join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t))
    (i : Fin (branch n)) (leaf : Slots branch n) (k : Fin t) :
    SourceChildKernel.tree designated i (join designated q positions i) leaf k =
      (q (i, leaf) k, positions (i, leaf) k) :=
  congrFun (congrFun (tree_join designated q positions) (i, leaf)) k

theorem sourceLaw_split [NeZero m] (designated : Fin (branch n) → Slots branch n) :
    (SourceChildQuestionLaw.sourceLaw m t designated).pushforward (split designated) =
      (PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m)).product
        (FiniteDistribution.uniform (Positions (branch := branch) (n := n) (t := t))) := by
  rw [SourceChildQuestionLaw.sourceLaw_uniform, FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (SourceChildKernel.Sources (m := m) (t := t) designated) : ℝ) =
    (1 / (Fintype.card (Questions (branch := branch) (n := n) (t := t) (m := m)) : ℝ)) *
      (1 / (Fintype.card (Positions (branch := branch) (n := n) (t := t)) : ℝ))
  rw [Fintype.card_congr (split (m := m) (t := t) designated), Fintype.card_prod,
    Nat.cast_mul, one_div_mul_one_div]

def byChild : Positions (branch := branch) (n := n) (t := t) ≃
    (Fin (branch n) → ChildPositions (branch := branch) (n := n) (t := t)) where
  toFun positions i leaf k := positions (i, leaf) k
  invFun positions leaf k := positions leaf.1 leaf.2 k
  left_inv _ := rfl
  right_inv _ := rfl

theorem positions_byChild :
    (FiniteDistribution.uniform (Positions (branch := branch) (n := n) (t := t))).pushforward
      (byChild (branch := branch) (n := n) (t := t)) =
      FiniteProduct.law (fun _ : Fin (branch n) =>
        FiniteDistribution.uniform (ChildPositions (branch := branch) (n := n) (t := t))) := by
  rw [UniformLinearImage.law_uniform, FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (Positions (branch := branch) (n := n) (t := t)) : ℝ) =
    1 / (Fintype.card (Fin (branch n) → ChildPositions (branch := branch) (n := n) (t := t)) : ℝ)
  rw [Fintype.card_congr (byChild (branch := branch) (n := n) (t := t))]

theorem parentLeftSlots_join {v : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    SourceChildKernel.parentLeftSlots clauses designated (join designated q positions) =
      HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q) := by
  rw [SourceChildQuestionLaw.parentLeftSlots_eq, questions_join]

end
end PerfectCompleteness.SourceQuestionPositionSplit

end

end OAI
