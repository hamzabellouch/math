import Mathlib.Tactic.Ring
import OAI.Computability.PerfectCompleteness.Foundations.WholeArraySubtreeSplit
import OAI.Computability.PerfectCompleteness.Sampling.WholeArrayHiddenLaw

namespace OAI

section

namespace PerfectCompleteness.WholeArrayInteriorHiddenLaw

open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler
open WholeArraySubtreeSplit
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

private def reorder (A H V R : Type*) :
    A × (H × (V × R)) ≃ H × (V × (A × R)) where
  toFun z := (z.2.1, (z.2.2.1, (z.1, z.2.2.2)))
  invFun z := (z.2.2.1, (z.1, (z.2.1, z.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem product_reorder {A H V R : Type*}
    [Fintype A] [Fintype H] [Fintype V] [Fintype R]
    (μ : FiniteDistribution A) (hidden : FiniteDistribution H)
    (visible : FiniteDistribution V) (rest : FiniteDistribution R) :
    (μ.product (hidden.product (visible.product rest))).pushforward (reorder A H V R) =
      hidden.product (visible.product (μ.product rest)) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨h, v, a, r⟩
  change μ.weight a * (hidden.weight h * (visible.weight v * rest.weight r)) =
    hidden.weight h * (visible.weight v * (μ.weight a * rest.weight r))
  ring

private theorem product_split_second {A B H V R : Type*}
    [Fintype A] [Fintype B] [Fintype H] [Fintype V] [Fintype R]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (hidden : FiniteDistribution H) (visible : FiniteDistribution V)
    (rest : FiniteDistribution R) (split : B → H × (V × R))
    (hsplit : ν.pushforward split = hidden.product (visible.product rest)) :
    (μ.product ν).pushforward
        (fun z => ((split z.2).1, ((split z.2).2.1, (z.1, (split z.2).2.2)))) =
      hidden.product (visible.product (μ.product rest)) := by
  calc
    _ = ((μ.product ν).pushforward (fun z => (z.1, split z.2))).pushforward
        (reorder A H V R) := by
      rw [FiniteDistribution.pushforward_comp]
      rfl
    _ = (μ.product (ν.pushforward split)).pushforward (reorder A H V R) := by
      rw [WholeArrayHiddenLaw.product_read_second]
    _ = _ := by
      rw [hsplit]
      exact product_reorder μ hidden visible rest

variable {branch : Nat → Nat} {N n m t : Nat}

abbrev ScalarTape (repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot) :=
  WholeArrayHiddenLaw.ScalarTape repeats i q (subtreeSlots p slots)

abbrev Exterior (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot) :=
  Complement rows repeats p (.step i q) slots ×
    WholeArrayHiddenLaw.RestTape rows repeats i q (subtreeSlots p slots)

def scalarLaw (repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot) :
    FiniteDistribution (ScalarTape repeats p i q slots) :=
  WholeArrayHiddenLaw.scalarLaw repeats i q (subtreeSlots p slots)

def exteriorLaw (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Exterior rows repeats p i q slots) :=
  (complementLaw rows repeats p (.step i q) slots).product
    (WholeArrayHiddenLaw.restLaw rows repeats i q (subtreeSlots p slots))

def split (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (ω : Tape rows repeats (p.append (.step i q)) slots) :
    HiddenBucketBias.HiddenTape W (ScalarTape repeats p i q slots) ×
      (HiddenBucketBias.VisibleTape W (ScalarTape repeats p i q slots) ×
        Exterior rows repeats p i q slots) :=
  let subtree := splitEquiv rows repeats p (.step i q) slots ω
  let buckets := WholeArrayHiddenLaw.split rows repeats i q (subtreeSlots p slots) W subtree.2
  (buckets.1, (buckets.2.1, (subtree.1, buckets.2.2)))

theorem split_hidden (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (ω : Tape rows repeats (p.append (.step i q)) slots) :
    (split rows repeats p i q slots W ω).1 =
      (WholeArrayHiddenLaw.split rows repeats i q (subtreeSlots p slots) W
        (extract rows repeats p (.step i q) slots ω)).1 := rfl

theorem split_law (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2)) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step i q)) slots).pushforward
        (split rows repeats p i q slots W) =
      (HiddenBucketBias.hiddenTapeLaw W (scalarLaw repeats p i q slots)).product
        ((HiddenBucketBias.visibleTapeLaw W (scalarLaw repeats p i q slots)).product
          (exteriorLaw rows repeats p i q slots)) := by
  let localSplit := WholeArrayHiddenLaw.split rows repeats i q (subtreeSlots p slots) W
  calc
    _ = ((WholeArraySampler.tapeLaw rows repeats (p.append (.step i q)) slots).pushforward
        (splitEquiv rows repeats p (.step i q) slots)).pushforward
          (fun z => ((localSplit z.2).1, ((localSplit z.2).2.1, (z.1, (localSplit z.2).2.2)))) := by
      rw [FiniteDistribution.pushforward_comp]
      rfl
    _ = _ := by
      rw [WholeArraySubtreeSplit.splitEquiv_tapeLaw]
      exact product_split_second
        (complementLaw rows repeats p (.step i q) slots)
        (WholeArraySampler.tapeLaw rows repeats (.step i q) (subtreeSlots p slots))
        (HiddenBucketBias.hiddenTapeLaw W (scalarLaw repeats p i q slots))
        (HiddenBucketBias.visibleTapeLaw W (scalarLaw repeats p i q slots))
        (WholeArrayHiddenLaw.restLaw rows repeats i q (subtreeSlots p slots)) localSplit
        (WholeArrayHiddenLaw.split_law rows repeats i q (subtreeSlots p slots) W)

theorem hidden_marginal (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2)) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step i q)) slots).pushforward
        (fun ω => (split rows repeats p i q slots W ω).1) =
      HiddenBucketBias.hiddenTapeLaw W (scalarLaw repeats p i q slots) := by
  rw [← FiniteDistribution.pushforward_comp
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step i q)) slots)
    (split rows repeats p i q slots W) Prod.fst, split_law, HiddenBucketBias.product_fst]

theorem split_readout_law {E : Type*} [Fintype E]
    (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (read : Exterior rows repeats p i q slots → E) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step i q)) slots).pushforward
        (fun ω => ((split rows repeats p i q slots W ω).1,
          ((split rows repeats p i q slots W ω).2.1,
            read (split rows repeats p i q slots W ω).2.2))) =
      HiddenBucketBias.exposedLaw W (scalarLaw repeats p i q slots)
        ((exteriorLaw rows repeats p i q slots).pushforward read) := by
  rw [← FiniteDistribution.pushforward_comp
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step i q)) slots)
    (split rows repeats p i q slots W)
    (fun z => (z.1, (z.2.1, read z.2.2))), split_law]
  let μ := HiddenBucketBias.hiddenTapeLaw W (scalarLaw repeats p i q slots)
  let ν := HiddenBucketBias.visibleTapeLaw W (scalarLaw repeats p i q slots)
  let ρ := exteriorLaw rows repeats p i q slots
  have inner :
      (ν.product ρ).pushforward
          (fun z : HiddenBucketBias.VisibleTape W (ScalarTape repeats p i q slots) ×
            Exterior rows repeats p i q slots => (z.1, read z.2)) =
        ν.product (ρ.pushforward read) :=
    WholeArrayHiddenLaw.product_read_second ν ρ read
  have outer :
      (μ.product (ν.product ρ)).pushforward
          (fun z : HiddenBucketBias.HiddenTape W (ScalarTape repeats p i q slots) ×
            (HiddenBucketBias.VisibleTape W (ScalarTape repeats p i q slots) ×
              Exterior rows repeats p i q slots) => (z.1, (z.2.1, read z.2.2))) =
        μ.product ((ν.product ρ).pushforward
          (fun z : HiddenBucketBias.VisibleTape W (ScalarTape repeats p i q slots) ×
            Exterior rows repeats p i q slots => (z.1, read z.2))) :=
    WholeArrayHiddenLaw.product_read_second μ (ν.product ρ)
      (fun z : HiddenBucketBias.VisibleTape W (ScalarTape repeats p i q slots) ×
        Exterior rows repeats p i q slots => (z.1, read z.2))
  exact outer.trans (congrArg
    (fun θ : FiniteDistribution
      (HiddenBucketBias.VisibleTape W (ScalarTape repeats p i q slots) × E) => μ.product θ)
    inner)

theorem split_observation_law {E : Type*} [Fintype E]
    (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (i : Fin (branch n)) (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch N → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows (n + 1)) → F2))
    (read : HiddenBucketBias.VisibleTape W (ScalarTape repeats p i q slots) ×
      Exterior rows repeats p i q slots → E) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step i q)) slots).pushforward
        (fun ω => ((split rows repeats p i q slots W ω).1,
          read (split rows repeats p i q slots W ω).2)) =
      (HiddenBucketBias.hiddenTapeLaw W (scalarLaw repeats p i q slots)).product
        (((HiddenBucketBias.visibleTapeLaw W (scalarLaw repeats p i q slots)).product
          (exteriorLaw rows repeats p i q slots)).pushforward read) := by
  rw [← FiniteDistribution.pushforward_comp
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step i q)) slots)
    (split rows repeats p i q slots W) (fun z => (z.1, read z.2)), split_law]
  exact WholeArrayHiddenLaw.product_read_second _ _ read

end
end PerfectCompleteness.WholeArrayInteriorHiddenLaw

end

end OAI
