import OAI.Computability.PerfectCompleteness.Construction.OriginalChildBlocks
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Foundations.GeometricPathLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness

namespace OAI

section

namespace PerfectCompleteness.OriginalHiddenChild

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

variable {branch : Nat → Nat} {n t : Nat}

abbrev Blocks (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  (child : Fin (branch n)) → ChildBlockCardinality.Raw calls rows (childSlots slots child)

abbrev Tape (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :=
  Σ leaf : Slots branch (n + 1), OriginalChildBlocks.SourceTape calls rows repeats
    leaf.1 (GeometricPath.leafPath leaf.2) slots

def sourceLaw (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n + 1, 0 < branch k) :
    FiniteDistribution (Tape calls rows repeats slots) :=
  CompletionSoundness.sigmaLaw (GeometricPath.law (n + 1) hbranch)
    (fun leaf => OriginalChildBlocks.sourceLaw calls rows repeats leaf.1
      (GeometricPath.leafPath leaf.2) slots)

def rawMap (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape calls rows repeats slots) : Blocks calls rows slots :=
  OriginalChildBlocks.rawMap calls rows repeats ω.1.1
    (GeometricPath.leafPath ω.1.2) slots ω.2

def continuationLaw (hbranch : ∀ k < n + 1, 0 < branch k) :
    FiniteDistribution (Slots branch n) :=
  GeometricPath.law n (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n)))

def averagedSpecial (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n + 1, 0 < branch k) (child : Fin (branch n)) :
    FiniteDistribution (ChildBlockCardinality.Raw calls rows (childSlots slots child)) :=
  (continuationLaw hbranch).mixture (fun leaf =>
    OriginalChildBlocks.specialLaw calls rows repeats (GeometricPath.leafPath leaf) slots child)

def blockMixture (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n + 1, 0 < branch k) : FiniteDistribution (Blocks calls rows slots) := by
  letI : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch n (Nat.lt_succ_self n)⟩⟩
  exact ChildBlockMixture.mixture (averagedSpecial calls rows repeats slots hbranch)

private theorem special_as_continued (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (chosen : Fin (branch n)) (leaf : Slots branch n) :
    ChildBlockMixture.special
        (OriginalChildBlocks.specialLaw calls rows repeats (GeometricPath.leafPath leaf) slots)
        chosen =
      ChildBlockContinuation.continuedSpecial
        (fun child leaf => OriginalChildBlocks.specialLaw calls rows repeats
          (GeometricPath.leafPath leaf) slots child) chosen leaf := by
  let : Nonempty (Fin (branch n)) := ⟨chosen⟩
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  rw [ChildBlockMixture.special_weight, ChildBlockContinuation.continuedSpecial_weight]

theorem rawMap_law (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n + 1, 0 < branch k) :
    (sourceLaw calls rows repeats slots hbranch).pushforward (rawMap calls rows repeats slots) =
      blockMixture calls rows repeats slots hbranch := by
  let : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch n (Nat.lt_succ_self n)⟩⟩
  refine (sigmaLaw_pushforward
    (E := Fin (branch n) × Slots branch n) (Γ := Blocks calls rows slots)
    (GeometricPath.law (n + 1) hbranch)
    (fun leaf => OriginalChildBlocks.sourceLaw calls rows repeats leaf.1
      (GeometricPath.leafPath leaf.2) slots)
    (fun leaf tape => OriginalChildBlocks.rawMap calls rows repeats leaf.1
      (GeometricPath.leafPath leaf.2) slots tape)).trans ?_
  simp_rw [OriginalChildBlocks.rawMap_law]
  rw [GeometricPath.law_step]
  refine (product_mixture (FiniteDistribution.uniform (Fin (branch n)))
    (continuationLaw hbranch)
    (fun tag : Fin (branch n) × Slots branch n =>
      ChildBlockMixture.special
        (OriginalChildBlocks.specialLaw calls rows repeats (GeometricPath.leafPath tag.2) slots)
        tag.1)).trans ?_
  simp_rw [special_as_continued]
  exact ChildBlockContinuation.uniform_average
    (fun _ : Fin (branch n) => continuationLaw hbranch)
    (fun child leaf => OriginalChildBlocks.specialLaw calls rows repeats
      (GeometricPath.leafPath leaf) slots child)

theorem rawMap_eq_mixture [Nonempty (Fin (branch n))]
    (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n + 1, 0 < branch k) :
    (sourceLaw calls rows repeats slots hbranch).pushforward (rawMap calls rows repeats slots) =
      ChildBlockMixture.mixture (averagedSpecial calls rows repeats slots hbranch) :=
  rawMap_law calls rows repeats slots hbranch

def observed (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape calls rows repeats slots) : CutChildGrouping.Assembled (C := Fin calls) slots rows :=
  OriginalChildBlocks.observed calls rows repeats ω.1.1
    (GeometricPath.leafPath ω.1.2) slots ω.2

theorem assemble_rawMap (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape calls rows repeats slots) :
    CutChildGrouping.assemble slots rows (rawMap calls rows repeats slots ω) =
      observed calls rows repeats slots ω :=
  OriginalChildBlocks.assemble_rawMap calls rows repeats ω.1.1
    (GeometricPath.leafPath ω.1.2) slots ω.2

theorem observed_law (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n + 1, 0 < branch k) :
    (sourceLaw calls rows repeats slots hbranch).pushforward (observed calls rows repeats slots) =
      (blockMixture calls rows repeats slots hbranch).pushforward
        (CutChildGrouping.assemble slots rows) := by
  rw [← rawMap_law calls rows repeats slots hbranch, FiniteDistribution.pushforward_comp]
  congr 1
  funext ω
  exact (assemble_rawMap calls rows repeats slots ω).symm

theorem raw_observed_variation {Γ : Type*} [Fintype Γ]
    (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n + 1, 0 < branch k) (observe : Blocks calls rows slots → Γ) :
    ((sourceLaw calls rows repeats slots hbranch).pushforward
        (fun ω => observe (rawMap calls rows repeats slots ω))).totalVariation
      ((ChildBlockMixture.reference (Ω := fun child : Fin (branch n) =>
        ChildBlockCardinality.Raw calls rows (childSlots slots child))).pushforward observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 /
        branch n) / 2 := by
  let : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch n (Nat.lt_succ_self n)⟩⟩
  have hpush : (sourceLaw calls rows repeats slots hbranch).pushforward
      (fun ω => observe (rawMap calls rows repeats slots ω)) =
      (blockMixture calls rows repeats slots hbranch).pushforward observe := by
    rw [← rawMap_law calls rows repeats slots hbranch]
    exact (FiniteDistribution.pushforward_comp _ _ _).symm
  rw [hpush]
  simpa only [blockMixture, Fintype.card_fin] using
    (ChildBlockMixture.actual_observed_variation calls rows (fun child => childSlots slots child)
      (averagedSpecial calls rows repeats slots hbranch) observe)

theorem observed_variation {Γ : Type*} [Fintype Γ]
    (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n + 1, 0 < branch k)
    (observe : CutChildGrouping.Assembled (C := Fin calls) slots rows → Γ) :
    ((sourceLaw calls rows repeats slots hbranch).pushforward
        (fun ω => observe (observed calls rows repeats slots ω))).totalVariation
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
  have h := raw_observed_variation calls rows repeats slots hbranch
    (fun x => observe (CutChildGrouping.assemble slots rows x))
  simpa only [assemble_rawMap, hclean] using h

end
end PerfectCompleteness.OriginalHiddenChild

end

end OAI
