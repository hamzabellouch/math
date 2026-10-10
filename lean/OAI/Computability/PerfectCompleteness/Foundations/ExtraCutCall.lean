import Mathlib.Algebra.BigOperators.Fin
import OAI.Computability.PerfectCompleteness.Sampling.NumberedUniformCut

namespace OAI

section

namespace PerfectCompleteness.ExtraCutCall

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

def splitLast (calls : Nat) (A : Type*) :
    (Fin (calls + 1) → A) ≃ (Fin calls → A) × A where
  toFun x := (fun i => x i.castSucc, x (Fin.last calls))
  invFun z := Fin.lastCases z.2 z.1
  left_inv x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc]
  right_inv z := by
    apply Prod.ext
    · funext i
      simp only [Fin.lastCases_castSucc]
    · simp only [Fin.lastCases_last]

theorem splitLast_law {A : Type*} [Fintype A] (calls : Nat) (μ : FiniteDistribution A) :
    (FiniteProduct.law (fun _ : Fin (calls + 1) => μ)).pushforward (splitLast calls A) =
      (FiniteProduct.law (fun _ : Fin calls => μ)).product μ := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨values, last⟩
  change (∏ i : Fin (calls + 1), μ.weight (Fin.lastCases last values i)) =
    (∏ i : Fin calls, μ.weight (values i)) * μ.weight last
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]

private def middleSwap (A B C : Type*) : (A × B) × C ≃ (A × C) × B where
  toFun z := ((z.1.1, z.2), z.1.2)
  invFun z := ((z.1.1, z.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem product_assoc_law {E A B : Type*}
    [Fintype E] [Fintype A] [Fintype B]
    (μ : FiniteDistribution E) (ν : FiniteDistribution A) (ξ : FiniteDistribution B) :
    (μ.product (ν.product ξ)).pushforward (fun z => ((z.1, z.2.1), z.2.2)) =
      (μ.product ν).product ξ := by
  change (μ.product (ν.product ξ)).pushforward (Equiv.prodAssoc E A B).symm = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  exact (mul_assoc _ _ _).symm

private theorem lift_split_law {E D A B : Type*}
    [Fintype E] [Fintype D] [Fintype A] [Fintype B]
    (μ : FiniteDistribution E) (ν : FiniteDistribution D)
    (ρ : FiniteDistribution A) (ξ : FiniteDistribution B) (split : D → A × B)
    (hsplit : ν.pushforward split = ρ.product ξ) :
    (μ.product ν).pushforward (fun z => ((z.1, (split z.2).1), (split z.2).2)) =
      (μ.product ρ).product ξ := by
  have hmap : (μ.product ν).pushforward (fun z => (z.1, split z.2)) =
      μ.product (ρ.product ξ) := by
    have h := FiniteDistribution.product_pushforward μ ν id split
    simpa only [id_eq, FiniteDistribution.pushforward_id, hsplit] using h
  calc
    _ = ((μ.product ν).pushforward (fun z => (z.1, split z.2))).pushforward
        (fun z => ((z.1, z.2.1), z.2.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (μ.product (ρ.product ξ)).pushforward
        (fun z => ((z.1, z.2.1), z.2.2)) :=
      congrArg (fun law : FiniteDistribution (E × (A × B)) =>
        law.pushforward (fun z => ((z.1, z.2.1), z.2.2))) hmap
    _ = _ := product_assoc_law μ ρ ξ

variable {branch : Nat → Nat} {n m k t : Nat}

def splitAssembled (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    CutChildGrouping.Assembled (C := Fin (calls + 1)) slots rows ≃
      CutChildGrouping.Assembled (C := Fin calls) slots rows × H slots :=
  (OriginalWholeCutBridge.assembledEquiv (calls + 1) rows slots).symm.trans
    ((Equiv.prodCongr (splitLast calls (H slots)) (Equiv.refl (ChildArrays rows slots))).trans
      ((middleSwap (Fin calls → H slots) (H slots) (ChildArrays rows slots)).trans
        (Equiv.prodCongr (OriginalWholeCutBridge.assembledEquiv calls rows slots)
          (Equiv.refl (H slots)))))

def observationLaw (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (CutChildGrouping.Assembled (C := Fin calls) slots rows) :=
  (OriginalChildBlocks.sourceLaw calls rows repeats chosen q slots).pushforward
    (OriginalChildBlocks.observed calls rows repeats chosen q slots)

theorem observation_split_law (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    (observationLaw (calls + 1) rows repeats chosen q slots).pushforward
        (splitAssembled calls rows slots) =
      (observationLaw calls rows repeats chosen q slots).product
        (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain slots)) := by
  simp only [observationLaw, OriginalWholeCutBridge.observed_product_law]
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  change ((∏ i : Fin (calls + 1),
      (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain slots)).weight
        (Fin.lastCases z.2 z.1.1 i)) *
      (belowArraysLaw rows repeats chosen q slots).weight z.1.2) =
    ((∏ i : Fin calls,
      (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain slots)).weight (z.1.1 i)) *
      (belowArraysLaw rows repeats chosen q slots).weight z.1.2) *
        (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain slots)).weight z.2
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  ring

theorem uniform_split_law (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin (calls + 1)) slots rows)).pushforward
        (splitAssembled calls rows slots) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) slots rows)).product
        (FiniteDistribution.uniform (H slots)) := by
  rw [← FiniteDistribution.transport_eq_pushforward, UniformConditioning.uniform_transport]
  exact WholeCutSampler.uniform_product.symm

abbrev EnlargedRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p slots × CutChildGrouping.Assembled
    (C := Fin (OriginalCutCalls.count rows repeats n (m + 1) + 1)) (cutSlots p slots) rows

def splitRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : EnlargedRecord rows repeats p slots) :
    OriginalWholeCutBridge.NumberedRecord rows repeats p slots × H (cutSlots p slots) :=
  let split := splitAssembled (OriginalCutCalls.count rows repeats n (m + 1)) rows
    (cutSlots p slots) record.2
  ((record.1, split.1), split.2)

@[simp] theorem splitRecord_oldCall (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : EnlargedRecord rows repeats p slots)
    (call : Fin (OriginalCutCalls.count rows repeats n (m + 1))) :
    (splitRecord rows repeats p slots record).1.2.1 call = record.2.1 call.castSucc := rfl

@[simp] theorem splitRecord_fresh (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : EnlargedRecord rows repeats p slots) :
    (splitRecord rows repeats p slots record).2 =
      record.2.1 (Fin.last (OriginalCutCalls.count rows repeats n (m + 1))) := rfl

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

theorem record_fresh_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((exteriorLaw rows repeats p slots).product
      (observationLaw (OriginalCutCalls.count rows repeats n (m + 1) + 1)
        rows repeats chosen q (cutSlots p slots))).pushforward (splitRecord rows repeats p slots) =
      ((recordLaw rows repeats p chosen q slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product
          (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))) := by
  rw [OriginalWholeCutBridge.numberRecord_law]
  exact lift_split_law (exteriorLaw rows repeats p slots) _ _ _
    (splitAssembled (OriginalCutCalls.count rows repeats n (m + 1)) rows (cutSlots p slots))
    (observation_split_law (OriginalCutCalls.count rows repeats n (m + 1))
      rows repeats chosen q (cutSlots p slots))

theorem uniform_record_fresh_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((exteriorLaw rows repeats p slots).product
      (FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (OriginalCutCalls.count rows repeats n (m + 1) + 1)) (cutSlots p slots) rows))).pushforward
        (splitRecord rows repeats p slots) =
      ((OriginalUniformCut.referenceLaw rows repeats p slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product
          (FiniteDistribution.uniform (H (cutSlots p slots))) := by
  rw [NumberedUniformCut.reference_numberRecord_law]
  exact lift_split_law (exteriorLaw rows repeats p slots) _ _ _
    (splitAssembled (OriginalCutCalls.count rows repeats n (m + 1)) rows (cutSlots p slots))
    (uniform_split_law (OriginalCutCalls.count rows repeats n (m + 1)) rows (cutSlots p slots))

def arraysAndFresh (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : EnlargedRecord rows repeats p slots) : Arrays slots rows × H (cutSlots p slots) :=
  (OriginalWholeCutBridge.reconstruct rows repeats p slots
    (splitRecord rows repeats p slots record).1, (splitRecord rows repeats p slots record).2)

theorem arrays_fresh_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((exteriorLaw rows repeats p slots).product
      (observationLaw (OriginalCutCalls.count rows repeats n (m + 1) + 1)
        rows repeats chosen q (cutSlots p slots))).pushforward (arraysAndFresh rows repeats p slots) =
      (WholeArraySampler.law rows repeats (p.append (.step chosen q)) slots).product
        (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))) := by
  calc
    _ = (((exteriorLaw rows repeats p slots).product
        (observationLaw (OriginalCutCalls.count rows repeats n (m + 1) + 1)
          rows repeats chosen q (cutSlots p slots))).pushforward
            (splitRecord rows repeats p slots)).pushforward
              (fun z => (OriginalWholeCutBridge.reconstruct rows repeats p slots z.1, z.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by
      rw [record_fresh_law, OriginalWholeCutBridge.numberRecord_law]
      have h := FiniteDistribution.product_pushforward
        ((exteriorLaw rows repeats p slots).product
          (observationLaw (OriginalCutCalls.count rows repeats n (m + 1))
            rows repeats chosen q (cutSlots p slots)))
        (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))
        (OriginalWholeCutBridge.reconstruct rows repeats p slots) id
      simpa only [id_eq, FiniteDistribution.pushforward_id,
        observationLaw, OriginalWholeCutBridge.reconstruct_child_law] using h

theorem uniform_arrays_fresh_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((exteriorLaw rows repeats p slots).product
      (FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (OriginalCutCalls.count rows repeats n (m + 1) + 1)) (cutSlots p slots) rows))).pushforward
      (arraysAndFresh rows repeats p slots) =
        (WholeArraySampler.law rows repeats p slots).product
          (FiniteDistribution.uniform (H (cutSlots p slots))) := by
  calc
    _ = (((exteriorLaw rows repeats p slots).product
        (FiniteDistribution.uniform (CutChildGrouping.Assembled
          (C := Fin (OriginalCutCalls.count rows repeats n (m + 1) + 1)) (cutSlots p slots) rows))).pushforward
          (splitRecord rows repeats p slots)).pushforward
            (fun z => (OriginalWholeCutBridge.reconstruct rows repeats p slots z.1, z.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by
      rw [uniform_record_fresh_law, NumberedUniformCut.reference_numberRecord_law]
      have h := FiniteDistribution.product_pushforward
        ((exteriorLaw rows repeats p slots).product
          (FiniteDistribution.uniform (CutChildGrouping.Assembled
            (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p slots) rows)))
        (FiniteDistribution.uniform (H (cutSlots p slots)))
        (OriginalWholeCutBridge.reconstruct rows repeats p slots) id
      simpa only [id_eq, FiniteDistribution.pushforward_id,
        NumberedUniformCut.reconstruct_product_uniform] using h

end
end PerfectCompleteness.ExtraCutCall

end

end OAI
