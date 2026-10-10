import OAI.Computability.PerfectCompleteness.Construction.OriginalChildBlocks
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Foundations.GeometricPathLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness

namespace OAI

section

namespace PerfectCompleteness.OriginalPrefixContinuation

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem sigmaLaw_pushforward {E Γ : Type*} {F : E → Type*}
    [Fintype E] [∀ e, Fintype (F e)] [Fintype Γ]
    (μ : FiniteDistribution E) (ν : ∀ e, FiniteDistribution (F e))
    (f : ∀ e, F e → Γ) :
    (CompletionSoundness.sigmaLaw μ ν).pushforward (fun x => f x.1 x.2) =
      μ.mixture (fun e => (ν e).pushforward (f e)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  simp only [FiniteDistribution.pushforward, CompletionSoundness.sigmaLaw,
    FiniteDistribution.mixture, Fintype.sum_sigma, Finset.mul_sum, mul_ite, mul_zero]

private theorem product_mixture {E F Γ : Type*}
    [Fintype E] [Fintype F] [Fintype Γ]
    (μ : FiniteDistribution E) (ν : FiniteDistribution F)
    (R : E × F → FiniteDistribution Γ) :
    (μ.product ν).mixture R = μ.mixture (fun e => ν.mixture (fun f => R (e, f))) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  simp only [FiniteDistribution.mixture, FiniteDistribution.product,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

variable {branch : Nat → Nat} {n k t : Nat} {K : Type*} [Fintype K]

abbrev Blocks (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  (child : Fin (branch n)) → ChildBlockCardinality.Raw calls rows (childSlots slots child)

abbrev Tape (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (q : K → Path branch n k) :=
  Σ tag : Fin (branch n) × K, OriginalChildBlocks.SourceTape calls rows repeats
    tag.1 (q tag.2) slots

def tagLaw (ν : FiniteDistribution K) (hbranch : 0 < branch n) :
    FiniteDistribution (Fin (branch n) × K) := by
  letI : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch⟩⟩
  exact (FiniteDistribution.uniform (Fin (branch n))).product ν

def sourceLaw (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k)
    (hbranch : 0 < branch n) :
    FiniteDistribution (Tape calls rows repeats slots q) :=
  CompletionSoundness.sigmaLaw (tagLaw ν hbranch)
    (fun tag => OriginalChildBlocks.sourceLaw calls rows repeats tag.1 (q tag.2) slots)

def rawMap (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (q : K → Path branch n k) (ω : Tape calls rows repeats slots q) : Blocks calls rows slots :=
  OriginalChildBlocks.rawMap calls rows repeats ω.1.1
    (q ω.1.2) slots ω.2

def averagedSpecial (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k)
    (_ : 0 < branch n) (child : Fin (branch n)) :
    FiniteDistribution (ChildBlockCardinality.Raw calls rows (childSlots slots child)) :=
  ν.mixture (fun tag => OriginalChildBlocks.specialLaw calls rows repeats (q tag) slots child)

def blockMixture (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k)
    (hbranch : 0 < branch n) : FiniteDistribution (Blocks calls rows slots) := by
  letI : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch⟩⟩
  exact ChildBlockMixture.mixture (averagedSpecial calls rows repeats slots ν q hbranch)

omit [Fintype K] in
private theorem special_as_continued (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (q : K → Path branch n k) (chosen : Fin (branch n)) (tag : K) :
    ChildBlockMixture.special
        (OriginalChildBlocks.specialLaw calls rows repeats (q tag) slots)
        chosen =
      ChildBlockContinuation.continuedSpecial
        (fun child tag => OriginalChildBlocks.specialLaw calls rows repeats
          (q tag) slots child) chosen tag := by
  let : Nonempty (Fin (branch n)) := ⟨chosen⟩
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  rw [ChildBlockMixture.special_weight, ChildBlockContinuation.continuedSpecial_weight]

theorem rawMap_law (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k)
    (hbranch : 0 < branch n) :
    (sourceLaw calls rows repeats slots ν q hbranch).pushforward (rawMap calls rows repeats slots q) =
      blockMixture calls rows repeats slots ν q hbranch := by
  let : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch⟩⟩
  refine (sigmaLaw_pushforward
    (E := Fin (branch n) × K) (Γ := Blocks calls rows slots)
    (tagLaw ν hbranch)
    (fun tag => OriginalChildBlocks.sourceLaw calls rows repeats tag.1 (q tag.2) slots)
    (fun tag tape => OriginalChildBlocks.rawMap calls rows repeats tag.1
      (q tag.2) slots tape)).trans ?_
  simp_rw [OriginalChildBlocks.rawMap_law]
  rw [tagLaw, product_mixture]
  simp_rw [special_as_continued]
  exact ChildBlockContinuation.uniform_average
    (fun _ : Fin (branch n) => ν)
    (fun child tag => OriginalChildBlocks.specialLaw calls rows repeats
      (q tag) slots child)

theorem rawMap_eq_mixture [Nonempty (Fin (branch n))]
    (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k)
    (hbranch : 0 < branch n) :
    (sourceLaw calls rows repeats slots ν q hbranch).pushforward (rawMap calls rows repeats slots q) =
      ChildBlockMixture.mixture (averagedSpecial calls rows repeats slots ν q hbranch) :=
  rawMap_law calls rows repeats slots ν q hbranch

def observed (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (q : K → Path branch n k) (ω : Tape calls rows repeats slots q) : CutChildGrouping.Assembled (C := Fin calls) slots rows :=
  OriginalChildBlocks.observed calls rows repeats ω.1.1
    (q ω.1.2) slots ω.2

omit [Fintype K] in
theorem assemble_rawMap (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (q : K → Path branch n k) (ω : Tape calls rows repeats slots q) :
    CutChildGrouping.assemble slots rows (rawMap calls rows repeats slots q ω) =
      observed calls rows repeats slots q ω :=
  OriginalChildBlocks.assemble_rawMap calls rows repeats ω.1.1
    (q ω.1.2) slots ω.2

theorem observed_law (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k)
    (hbranch : 0 < branch n) :
    (sourceLaw calls rows repeats slots ν q hbranch).pushforward (observed calls rows repeats slots q) =
      (blockMixture calls rows repeats slots ν q hbranch).pushforward
        (CutChildGrouping.assemble slots rows) := by
  rw [← rawMap_law calls rows repeats slots ν q hbranch, FiniteDistribution.pushforward_comp]
  congr 1
  funext ω
  exact (assemble_rawMap calls rows repeats slots q ω).symm

theorem raw_observed_variation {Γ : Type*} [Fintype Γ]
    (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k)
    (hbranch : 0 < branch n) (observe : Blocks calls rows slots → Γ) :
    ((sourceLaw calls rows repeats slots ν q hbranch).pushforward
        (fun ω => observe (rawMap calls rows repeats slots q ω))).totalVariation
      ((ChildBlockMixture.reference (Ω := fun child : Fin (branch n) =>
        ChildBlockCardinality.Raw calls rows (childSlots slots child))).pushforward observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 /
        branch n) / 2 := by
  let : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch⟩⟩
  have hpush : (sourceLaw calls rows repeats slots ν q hbranch).pushforward
      (fun ω => observe (rawMap calls rows repeats slots q ω)) =
      (blockMixture calls rows repeats slots ν q hbranch).pushforward observe := by
    rw [← rawMap_law calls rows repeats slots ν q hbranch]
    exact (FiniteDistribution.pushforward_comp _ _ _).symm
  rw [hpush]
  simpa only [blockMixture, Fintype.card_fin] using
    (ChildBlockMixture.actual_observed_variation calls rows
      (fun child => childSlots slots child)
      (averagedSpecial calls rows repeats slots ν q hbranch) observe)

theorem observed_variation {Γ : Type*} [Fintype Γ]
    (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k)
    (hbranch : 0 < branch n)
    (observe : CutChildGrouping.Assembled (C := Fin calls) slots rows → Γ) :
    ((sourceLaw calls rows repeats slots ν q hbranch).pushforward
        (fun ω => observe (observed calls rows repeats slots q ω))).totalVariation
      ((FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) slots rows)).pushforward
        observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 /
        branch n) / 2 := by
  have hclean : (ChildBlockMixture.reference (Ω := fun child : Fin (branch n) =>
      ChildBlockCardinality.Raw calls rows (childSlots slots child))).pushforward
        (fun x => observe (CutChildGrouping.assemble slots rows x)) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) slots rows)).pushforward
        observe := by
    rw [← FiniteDistribution.pushforward_comp]
    have h := CutChildGrouping.assemble_law (C := Fin calls) slots rows
    change (ChildBlockMixture.reference (Ω := fun child : Fin (branch n) =>
      ChildBlockCardinality.Raw calls rows (childSlots slots child))).pushforward
        (CutChildGrouping.assemble slots rows) = _ at h
    rw [h]
  have h := raw_observed_variation calls rows repeats slots ν q hbranch
    (fun x => observe (CutChildGrouping.assemble slots rows x))
  simpa only [assemble_rawMap, hclean] using h

def assembledLaw (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n) :
    FiniteDistribution (CutChildGrouping.Assembled (C := Fin calls) slots rows) :=
  (sourceLaw calls rows repeats slots ν q hbranch).pushforward
    (observed calls rows repeats slots q)

theorem assembledLaw_eq_mixture (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n) :
    assembledLaw calls rows repeats slots ν q hbranch =
      (tagLaw ν hbranch).mixture (fun tag =>
        (OriginalChildBlocks.sourceLaw calls rows repeats tag.1 (q tag.2) slots).pushforward
          (OriginalChildBlocks.observed calls rows repeats tag.1 (q tag.2) slots)) := by
  exact sigmaLaw_pushforward
    (E := Fin (branch n) × K)
    (Γ := CutChildGrouping.Assembled (C := Fin calls) slots rows)
    (tagLaw ν hbranch)
    (fun tag => OriginalChildBlocks.sourceLaw calls rows repeats tag.1 (q tag.2) slots)
    (fun tag tape => OriginalChildBlocks.observed calls rows repeats tag.1
      (q tag.2) slots tape)

theorem assembledLaw_variation (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n) :
    (assembledLaw calls rows repeats slots ν q hbranch).totalVariation
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) slots rows)) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 /
        branch n) / 2 := by
  simpa only [id_eq, FiniteDistribution.pushforward_id, assembledLaw] using
    observed_variation calls rows repeats slots ν q hbranch
      (id : CutChildGrouping.Assembled (C := Fin calls) slots rows →
        CutChildGrouping.Assembled (C := Fin calls) slots rows)

end
end PerfectCompleteness.OriginalPrefixContinuation

end

end OAI
