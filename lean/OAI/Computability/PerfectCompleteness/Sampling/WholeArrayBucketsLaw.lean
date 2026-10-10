import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayInteriorExteriorLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas

namespace OAI

section

namespace PerfectCompleteness.WholeArrayBucketsLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySampler WholeArraySubtreeSplit
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

private def reorder (A B C : Type*) : A × (B × C) ≃ B × (A × C) where
  toFun z := (z.2.1, (z.1, z.2.2))
  invFun z := (z.2.1, (z.1, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem product_reorder {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (ρ : FiniteDistribution C) :
    (μ.product (ν.product ρ)).pushforward (reorder A B C) = ν.product (μ.product ρ) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  exact mul_left_comm _ _ _

private theorem product_swap {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    (μ.product ν).pushforward (Equiv.prodComm A B) = ν.product μ := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  exact mul_comm _ _

private theorem product_readout_swap {A B V W : Type*}
    [Fintype A] [Fintype B] [Fintype V] [Fintype W]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (f : A → V) (g : B → W) :
    (μ.product ν).pushforward (fun z => (g z.2, f z.1)) =
      (ν.pushforward g).product (μ.pushforward f) := by
  calc
    _ = ((μ.product ν).pushforward (fun z : A × B => (f z.1, g z.2))).pushforward
        (Equiv.prodComm V W) :=
      (FiniteDistribution.pushforward_comp (μ.product ν)
        (fun z : A × B => (f z.1, g z.2)) (Equiv.prodComm V W)).symm
    _ = ((μ.pushforward f).product (ν.pushforward g)).pushforward (Equiv.prodComm V W) :=
      congrArg (fun law : FiniteDistribution (V × W) => law.pushforward (Equiv.prodComm V W))
        (FiniteDistribution.product_pushforward μ ν f g)
    _ = _ := product_swap (μ.pushforward f) (ν.pushforward g)

variable {branch : Nat → Nat} {N n m t : Nat}

def split (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots) :
    BucketSampler.Tape (rows (n + 1))
        (WholeArrayInteriorHiddenLaw.ScalarTape repeats p chosen q slots) ×
      WholeArrayInteriorHiddenLaw.Exterior rows repeats p chosen q slots :=
  let subtree := WholeArraySubtreeSplit.splitEquiv rows repeats p (.step chosen q) slots tape
  (subtree.2 (.inl ()), (subtree.1, fun field => subtree.2 field.val))

@[simp] theorem split_fst (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots) :
    (split rows repeats p chosen q slots tape).1 =
      (WholeArraySubtreeSplit.extract rows repeats p (.step chosen q) slots tape) (.inl ()) := rfl

@[simp] theorem split_snd (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots) :
    (split rows repeats p chosen q slots tape).2 =
      WholeArrayInteriorExterior.read rows repeats p chosen q slots tape := rfl

theorem split_law (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
      (split rows repeats p chosen q slots) =
      (BucketSampler.tapeLaw (rows (n + 1))
        (WholeArrayInteriorHiddenLaw.scalarLaw repeats p chosen q slots)).product
          (WholeArrayInteriorHiddenLaw.exteriorLaw rows repeats p chosen q slots) := by
  let ancestor := WholeArraySubtreeSplit.complementLaw rows repeats p (.step chosen q) slots
  let subtree := WholeArraySampler.tapeLaw rows repeats (.step chosen q) (subtreeSlots p slots)
  let localSplit := WholeArrayHiddenLaw.splitRoot rows repeats chosen q (subtreeSlots p slots)
  calc
    _ = ((WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
        (WholeArraySubtreeSplit.splitEquiv rows repeats p (.step chosen q) slots)).pushforward
          (fun z => reorder _ _ _ (z.1, localSplit z.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (ancestor.product subtree).pushforward (fun z => reorder _ _ _ (z.1, localSplit z.2)) := by
      rw [WholeArraySubtreeSplit.splitEquiv_tapeLaw]
    _ = ((ancestor.product subtree).pushforward (fun z => (z.1, localSplit z.2))).pushforward
        (reorder _ _ _) := (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (ancestor.product (subtree.pushforward localSplit)).pushforward (reorder _ _ _) := by
      rw [WholeArrayHiddenLaw.product_read_second]
    _ = _ := by
      dsimp only [subtree, localSplit]
      rw [WholeArrayHiddenLaw.splitRoot_law, product_reorder]
      rfl

def readout {V B : Type*} (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (value : WholeArrayInteriorHiddenLaw.ScalarTape repeats p chosen q slots → V)
    (background : WholeArrayInteriorHiddenLaw.Exterior rows repeats p chosen q slots → B)
    (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots) :
    B × BucketSampler.Tape (rows (n + 1)) V :=
  (background (split rows repeats p chosen q slots tape).2,
    fun direction => value ((split rows repeats p chosen q slots tape).1 direction))

theorem readout_law {V B : Type*} [Fintype V] [Fintype B]
    (rows repeats : Nat → Nat) (p : Path branch N (n + 1))
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (value : WholeArrayInteriorHiddenLaw.ScalarTape repeats p chosen q slots → V)
    (background : WholeArrayInteriorHiddenLaw.Exterior rows repeats p chosen q slots → B) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
      (readout rows repeats p chosen q slots value background) =
      ((WholeArrayInteriorHiddenLaw.exteriorLaw rows repeats p chosen q slots).pushforward background).product
        (BucketSampler.tapeLaw (rows (n + 1))
          ((WholeArrayInteriorHiddenLaw.scalarLaw repeats p chosen q slots).pushforward value)) := by
  let buckets := BucketSampler.tapeLaw (rows (n + 1))
    (WholeArrayInteriorHiddenLaw.scalarLaw repeats p chosen q slots)
  let exterior := WholeArrayInteriorHiddenLaw.exteriorLaw rows repeats p chosen q slots
  have hvalues : buckets.pushforward (fun tapes direction => value (tapes direction)) =
      BucketSampler.tapeLaw (rows (n + 1))
        ((WholeArrayInteriorHiddenLaw.scalarLaw repeats p chosen q slots).pushforward value) :=
    FiniteProduct.pushforward_map
      (fun _ : BucketSampler.Direction (rows (n + 1)) =>
        WholeArrayInteriorHiddenLaw.scalarLaw repeats p chosen q slots)
      (fun _ => value)
  calc
    _ = ((WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
        (split rows repeats p chosen q slots)).pushforward
          (fun z => (background z.2, fun direction => value (z.1 direction))) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (buckets.product exterior).pushforward
        (fun z => (background z.2, fun direction => value (z.1 direction))) := by rw [split_law]
    _ = (exterior.pushforward background).product
        (buckets.pushforward (fun tapes direction => value (tapes direction))) :=
      product_readout_swap buckets exterior (fun tapes direction => value (tapes direction)) background
    _ = _ := by rw [hvalues]

end
end PerfectCompleteness.WholeArrayBucketsLaw

end

end OAI
