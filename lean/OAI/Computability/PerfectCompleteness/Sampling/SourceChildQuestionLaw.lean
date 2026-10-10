import OAI.Computability.PerfectCompleteness.Construction.HiddenBucketBias
import OAI.Computability.PerfectCompleteness.Sampling.PreliminarySampler
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildKernelMarginalLemmas

namespace OAI

section

namespace PerfectCompleteness.SourceChildQuestionLaw

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays SourceQuestionReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t v : Nat}

def sourceLaw (m t : Nat) [NeZero m] (designated : Fin (branch n) → Slots branch n) :
    FiniteDistribution (SourceChildKernel.Sources (m := m) (t := t) designated) :=
  FiniteProduct.law (fun i => (SourceOddLists.tupleLaw m t).product
    (FiniteProduct.law (fun _ : {leaf : Slots branch n // leaf ≠ designated i} =>
      SourceOddLists.tupleLaw m t)))

def assembleEquiv (designated : Fin (branch n) → Slots branch n) :
    SourceChildKernel.Sources (m := m) (t := t) designated ≃
      (Slots branch (n + 1) → SourceTuple m t) where
  toFun sources leaf := CleanSourceRecord.assemble designated leaf.1
    (sources leaf.1).1 (sources leaf.1).2 leaf.2
  invFun tree i := (Equiv.piSplitAt (designated i) (fun _ : Slots branch n => SourceTuple m t))
    (fun leaf => tree (i, leaf))
  left_inv sources := by
    funext i
    exact (Equiv.piSplitAt (designated i) (fun _ : Slots branch n => SourceTuple m t)).apply_symm_apply
      (sources i)
  right_inv tree := by
    funext leaf
    exact congrFun
      ((Equiv.piSplitAt (designated leaf.1) (fun _ : Slots branch n => SourceTuple m t)).symm_apply_apply
        (fun s => tree (leaf.1, s))) leaf.2

theorem assemble_child_law (designated : Fin (branch n) → Slots branch n)
    (μ : FiniteDistribution (SourceTuple m t)) (i : Fin (branch n)) :
    (μ.product (FiniteProduct.law
      (fun _ : {leaf : Slots branch n // leaf ≠ designated i} => μ))).pushforward
        (fun source => CleanSourceRecord.assemble designated i source.1 source.2) =
      FiniteProduct.law (fun _ : Slots branch n => μ) := by
  let split := Equiv.piSplitAt (designated i) (fun _ : Slots branch n => SourceTuple m t)
  have hsplit : (FiniteProduct.law (fun _ : Slots branch n => μ)).pushforward split =
      μ.product (FiniteProduct.law
        (fun _ : {leaf : Slots branch n // leaf ≠ designated i} => μ)) :=
    SourceCoordinateSplit.coordinate_split_pushforward (fun _ : Slots branch n => μ) (designated i)
  change (μ.product (FiniteProduct.law
    (fun _ : {leaf : Slots branch n // leaf ≠ designated i} => μ))).pushforward split.symm = _
  rw [← hsplit, FiniteDistribution.pushforward_comp]
  simp only [Equiv.symm_apply_apply]
  exact UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
    (FiniteProduct.law (fun _ : Slots branch n => μ))

private theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (FiniteDistribution.uniform A).product (FiniteDistribution.uniform B) =
      FiniteDistribution.uniform (A × B) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]

private theorem uniform_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ≃ B) :
    (FiniteDistribution.uniform A).pushforward e = FiniteDistribution.uniform B := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card A : ℝ) = 1 / (Fintype.card B : ℝ)
  rw [Fintype.card_congr e]

theorem sourceLaw_uniform [NeZero m] (designated : Fin (branch n) → Slots branch n) :
    sourceLaw m t designated =
      FiniteDistribution.uniform (SourceChildKernel.Sources (m := m) (t := t) designated) := by
  simp only [sourceLaw, SourceOddLists.tupleLaw, FiniteDistribution.iid_uniform,
    UniformLinearImage.law_uniform, uniform_product]

theorem assemble_law [NeZero m] (designated : Fin (branch n) → Slots branch n) :
    (sourceLaw m t designated).pushforward (assembleEquiv (m := m) (t := t) designated) =
      FiniteDistribution.uniform (Slots branch (n + 1) → SourceTuple m t) := by
  rw [sourceLaw_uniform]
  exact uniform_equiv _

def questions (designated : Fin (branch n) → Slots branch n)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    PreliminarySampler.Questions branch (n + 1) t m :=
  fun leaf k => (assembleEquiv designated sources leaf k).1

private def splitPositions :
    (Slots branch (n + 1) → SourceTuple m t) ≃
      (PreliminarySampler.Questions branch (n + 1) t m ×
        (Slots branch (n + 1) → Fin t → Fin 3)) where
  toFun tree := (fun leaf k => (tree leaf k).1, fun leaf k => (tree leaf k).2)
  invFun parts leaf k := (parts.1 leaf k, parts.2 leaf k)
  left_inv _ := rfl
  right_inv _ := rfl

theorem questions_law [NeZero m] (designated : Fin (branch n) → Slots branch n) :
    (sourceLaw m t designated).pushforward (questions designated) =
      PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m) := by
  let e := splitPositions (branch := branch) (n := n) (m := m) (t := t)
  calc
    _ = (((sourceLaw m t designated).pushforward
        (assembleEquiv (m := m) (t := t) designated)).pushforward e).pushforward Prod.fst := by
      rw [FiniteDistribution.pushforward_comp, FiniteDistribution.pushforward_comp]; rfl
    _ = ((FiniteDistribution.uniform (Slots branch (n + 1) → SourceTuple m t)).pushforward e).pushforward
        Prod.fst := by rw [assemble_law]
    _ = (FiniteDistribution.uniform
        (PreliminarySampler.Questions branch (n + 1) t m ×
          (Slots branch (n + 1) → Fin t → Fin 3))).pushforward Prod.fst := by
      rw [uniform_equiv]
    _ = _ := by
      rw [← uniform_product, HiddenBucketBias.product_fst]; rfl

theorem parentLeftSlots_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch n) → Slots branch n)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    SourceChildKernel.parentLeftSlots clauses designated sources =
      HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints (questions designated sources)) := rfl

theorem originalLaw_sources {C : Type*} [Fintype C] [NeZero m]
    (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch n) → Slots branch n)
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (SourceChildKernelMarginal.sources rows clauses designated) = sourceLaw m t designated :=
  SourceChildKernelMarginal.originalLaw_sources rows clauses designated flag

theorem originalLaw_questions {C : Type*} [Fintype C] [NeZero m]
    (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch n) → Slots branch n)
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (fun sample => questions designated (SourceChildKernelMarginal.sources rows clauses designated sample)) =
      PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m) := by
  rw [← FiniteDistribution.pushforward_comp
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag)
    (SourceChildKernelMarginal.sources rows clauses designated) (questions designated), originalLaw_sources]
  exact questions_law designated

end
end PerfectCompleteness.SourceChildQuestionLaw

end

end OAI
