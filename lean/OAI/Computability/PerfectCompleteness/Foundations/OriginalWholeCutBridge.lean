import OAI.Computability.PerfectCompleteness.Construction.OriginalChildBlocks
import OAI.Computability.PerfectCompleteness.Sampling.OriginalWholeCutLaw

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutBridge

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

private theorem pair_map_transport {A B C D Z : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype Z]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (f : A → C) (g : B → D) (e : C × D ≃ Z) :
    (μ.product ν).pushforward (fun x => e (f x.1, g x.2)) =
      ((μ.pushforward f).product (ν.pushforward g)).transport e := by
  rw [FiniteDistribution.transport_eq_pushforward]
  calc
    _ = ((μ.product ν).pushforward (fun x => (f x.1, g x.2))).pushforward e :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := congrArg (fun ρ : FiniteDistribution (C × D) => ρ.pushforward e)
      (FiniteDistribution.product_pushforward μ ν f g)

private theorem product_pair_map {E A B C Z : Type*}
    [Fintype E] [Fintype A] [Fintype B] [Fintype C] [Fintype Z]
    (μ : FiniteDistribution E) (ν : FiniteDistribution A) (ξ : FiniteDistribution B)
    (f : A → C) (e : C × B ≃ Z) :
    (μ.product (ν.product ξ)).pushforward (fun x => (x.1, e (f x.2.1, x.2.2))) =
      μ.product (((ν.pushforward f).product ξ).transport e) := by
  have hpair : (ν.product ξ).pushforward (fun x => e (f x.1, x.2)) =
      ((ν.pushforward f).product ξ).transport e := by
    simpa only [id_eq, FiniteDistribution.pushforward_id] using
      (pair_map_transport ν ξ f (id : B → B) e)
  calc
    _ = (μ.pushforward id).product
        ((ν.product ξ).pushforward (fun x => e (f x.1, x.2))) :=
      FiniteDistribution.product_pushforward μ (ν.product ξ) id
        (fun x => e (f x.1, x.2))
    _ = _ := congrArg₂
      (fun (ρ : FiniteDistribution E) (σ : FiniteDistribution Z) => ρ.product σ)
      (FiniteDistribution.pushforward_id μ) hpair

variable {branch : Nat → Nat} {n m k t : Nat}

def assembledEquiv (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    ((Fin calls → H slots) × ChildArrays rows slots) ≃
      CutChildGrouping.Assembled (C := Fin calls) slots rows := Equiv.refl _

def scalarValuesLaw (calls : Nat) (repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Fin calls → H slots) :=
  FiniteProduct.law (fun _ : Fin calls =>
    RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain slots))

theorem observed_product_law (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    (OriginalChildBlocks.sourceLaw calls rows repeats chosen q slots).pushforward
        (OriginalChildBlocks.observed calls rows repeats chosen q slots) =
      @FiniteDistribution.transport
        ((Fin calls → H slots) × ChildArrays rows slots)
        (CutChildGrouping.Assembled (C := Fin calls) slots rows)
        (instFintypeProd _ _) (CutChildGrouping.assembledFintype (C := Fin calls) slots rows)
        ((scalarValuesLaw calls repeats chosen q slots).product
          (belowArraysLaw rows repeats chosen q slots))
        (assembledEquiv calls rows slots) := by
  have hcalls : (OriginalChildScalars.callsLaw calls repeats chosen q slots).pushforward
      (fun tapes call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
        (LeafDomain slots) (tapes call)) = scalarValuesLaw calls repeats chosen q slots :=
    FiniteProduct.pushforward_map
      (fun _ : Fin calls => RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain slots))
      (fun _ => RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain slots))
  have hmap := pair_map_transport
    (A := Fin calls → OriginalChildScalars.ScalarTape repeats chosen q slots)
    (B := WholeArraySampler.Tape rows repeats (.step chosen q) slots)
    (C := Fin calls → H slots) (D := ChildArrays rows slots)
    (Z := CutChildGrouping.Assembled (C := Fin calls) slots rows)
    (OriginalChildScalars.callsLaw calls repeats chosen q slots)
    (WholeArraySampler.tapeLaw rows repeats (.step chosen q) slots)
    (fun tapes call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain slots) (tapes call))
    (OriginalBelowCut.below rows repeats chosen q slots)
    (assembledEquiv calls rows slots)
  rw [hcalls, OriginalBelowCut.below_pushforward] at hmap
  exact hmap

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

abbrev NumberedRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p slots ×
    CutChildGrouping.Assembled
      (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p slots) rows

def numberRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) : NumberedRecord rows repeats p slots :=
  (record.1, assembledEquiv (OriginalCutCalls.count rows repeats n (m + 1)) rows
    (cutSlots p slots) (numberedValues rows repeats p slots record.2.1, record.2.2))

def reconstruct (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : NumberedRecord rows repeats p slots) : Arrays slots rows :=
  reconstructNumbered rows repeats p slots record.1 record.2.1 record.2.2

theorem reconstruct_numberRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (record : Record rows repeats p slots) :
    reconstruct rows repeats p slots (numberRecord rows repeats p slots record) =
      reconstructRecord rows repeats p slots record :=
  reconstructNumbered_numberedValues rows repeats p slots record.1 record.2.1 record.2.2

theorem numberRecord_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (recordLaw rows repeats p chosen q slots).pushforward (numberRecord rows repeats p slots) =
      (exteriorLaw rows repeats p slots).product
        ((OriginalChildBlocks.sourceLaw (OriginalCutCalls.count rows repeats n (m + 1))
          rows repeats chosen q (cutSlots p slots)).pushforward
            (OriginalChildBlocks.observed (OriginalCutCalls.count rows repeats n (m + 1))
              rows repeats chosen q (cutSlots p slots))) := by
  have hmap := product_pair_map
    (E := Exterior rows repeats p slots)
    (A := Values rows repeats p slots) (B := BelowArrays rows p slots)
    (C := Fin (OriginalCutCalls.count rows repeats n (m + 1)) → H (cutSlots p slots))
    (Z := CutChildGrouping.Assembled
      (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p slots) rows)
    (exteriorLaw rows repeats p slots) (valuesLaw rows repeats p chosen q slots)
    (belowArraysLaw rows repeats chosen q (cutSlots p slots))
    (numberedValues rows repeats p slots)
    (assembledEquiv (OriginalCutCalls.count rows repeats n (m + 1)) rows (cutSlots p slots))
  rw [numberedValues_law] at hmap
  apply Eq.trans hmap
  exact congrArg
    (fun μ : FiniteDistribution (CutChildGrouping.Assembled
        (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p slots) rows) =>
      (exteriorLaw rows repeats p slots).product μ)
    (observed_product_law (OriginalCutCalls.count rows repeats n (m + 1)) rows repeats
      chosen q (cutSlots p slots)).symm

theorem reconstruct_child_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((exteriorLaw rows repeats p slots).product
        ((OriginalChildBlocks.sourceLaw (OriginalCutCalls.count rows repeats n (m + 1))
          rows repeats chosen q (cutSlots p slots)).pushforward
            (OriginalChildBlocks.observed (OriginalCutCalls.count rows repeats n (m + 1))
              rows repeats chosen q (cutSlots p slots)))).pushforward
                (reconstruct rows repeats p slots) =
      WholeArraySampler.law rows repeats (p.append (.step chosen q)) slots := by
  rw [← numberRecord_law rows repeats p chosen q slots, FiniteDistribution.pushforward_comp]
  have hmap : (fun record : Record rows repeats p slots =>
      reconstruct rows repeats p slots (numberRecord rows repeats p slots record)) =
      reconstructRecord rows repeats p slots :=
    funext (reconstruct_numberRecord rows repeats p slots)
  rw [hmap]
  exact reconstruct_law rows repeats p chosen q slots

theorem reconstruct_blocks_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((exteriorLaw rows repeats p slots).product
        ((ChildBlockMixture.special
          (OriginalChildBlocks.specialLaw (OriginalCutCalls.count rows repeats n (m + 1))
            rows repeats q (cutSlots p slots)) chosen).pushforward
              (CutChildGrouping.assemble (C := Fin (OriginalCutCalls.count rows repeats n (m + 1)))
                (cutSlots p slots) rows))).pushforward (reconstruct rows repeats p slots) =
      WholeArraySampler.law rows repeats (p.append (.step chosen q)) slots := by
  rw [← OriginalChildBlocks.observed_law]
  exact reconstruct_child_law rows repeats p chosen q slots

end
end PerfectCompleteness.OriginalWholeCutBridge

end

end OAI
