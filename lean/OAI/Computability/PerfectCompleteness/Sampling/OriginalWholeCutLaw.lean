import OAI.Computability.PerfectCompleteness.Construction.OriginalChildBlockProducts
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Foundations.OriginalWholeCut

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem product_map_record {E A B V D : Type*}
    [Fintype E] [Fintype A] [Fintype B] [Fintype V] [Fintype D]
    (exterior : FiniteDistribution E) (calls : FiniteDistribution A)
    (below : FiniteDistribution B) (values : A → V) (arrays : B → D) :
    (exterior.product (calls.product below)).pushforward
        (fun z => (z.1, (values z.2.1, arrays z.2.2))) =
      exterior.product ((calls.pushforward values).product (below.pushforward arrays)) := by
  calc
    _ = (exterior.pushforward id).product
        ((calls.product below).pushforward (fun z => (values z.1, arrays z.2))) :=
      FiniteDistribution.product_pushforward exterior (calls.product below) id
        (fun z => (values z.1, arrays z.2))
    _ = _ := by rw [FiniteDistribution.pushforward_id, FiniteDistribution.product_pushforward]

variable {branch : Nat → Nat} {n m k t : Nat}

@[instance_reducible] def valuesBelowFintype (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (OriginalWholeCut.Values rows repeats p slots ×
      OriginalWholeCut.BelowArrays rows p slots) :=
  @instFintypeProd (OriginalWholeCut.Values rows repeats p slots)
    (OriginalWholeCut.BelowArrays rows p slots) inferInstance inferInstance

attribute [local instance 2000] valuesBelowFintype

theorem childrenAt_law (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (chosen : Fin (branch m))
    (Q : (child : Fin (branch m)) →
      FiniteDistribution (Arrays (childSlots slots child) rows)) :
    ((Q chosen).product (FiniteProduct.law
        (fun child : RecursiveSampler.OffPath chosen =>
          FiniteDistribution.uniform (Arrays (childSlots slots child.val) rows)))).pushforward
        (fun z => WholeArraySampler.childrenAt slots rows chosen z.1 z.2) =
      FiniteProduct.law (ChildBlockMixture.component Q chosen) := by
  have hselected : ChildBlockMixture.component Q chosen chosen = Q chosen := dite_eq_left rfl
  have hother : FiniteProductSplit.otherLaw (ChildBlockMixture.component Q chosen) chosen =
      FiniteProduct.law (fun child : RecursiveSampler.OffPath chosen =>
        FiniteDistribution.uniform (Arrays (childSlots slots child.val) rows)) := by
    apply congrArg (fun laws : (child : RecursiveSampler.OffPath chosen) →
      FiniteDistribution (Arrays (childSlots slots child.val) rows) => FiniteProduct.law laws)
    funext child
    exact dite_eq_right (Ne.symm child.property)
  have h := OriginalChildBlockProducts.merge_law (ChildBlockMixture.component Q chosen) chosen
  rw [hselected, hother] at h
  exact h

def belowArraysLaw (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution ((child : Fin (branch m)) → Arrays (childSlots slots child) rows) :=
  FiniteProduct.law (ChildBlockMixture.component
    (fun child => WholeArraySampler.law rows repeats q (childSlots slots child)) chosen)

theorem below_product_law (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    ((WholeArraySampler.tapeLaw rows repeats q (childSlots slots chosen)).product
        (FiniteProduct.law (fun child : RecursiveSampler.OffPath chosen =>
          FiniteDistribution.uniform (Arrays (childSlots slots child.val) rows)))).pushforward
        (fun z => WholeArraySampler.childrenAt slots rows chosen
          (WholeArraySampler.evaluate rows repeats q (childSlots slots chosen) z.1) z.2) =
      belowArraysLaw rows repeats chosen q slots := by
  let ordinary := FiniteProduct.law (fun child : RecursiveSampler.OffPath chosen =>
    FiniteDistribution.uniform (Arrays (childSlots slots child.val) rows))
  calc
    _ = (((WholeArraySampler.tapeLaw rows repeats q (childSlots slots chosen)).product
        ordinary).pushforward (fun z =>
          (WholeArraySampler.evaluate rows repeats q (childSlots slots chosen) z.1,
            z.2))).pushforward
              (fun z => WholeArraySampler.childrenAt slots rows chosen z.1 z.2) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = ((WholeArraySampler.law rows repeats q (childSlots slots chosen)).product
        ordinary).pushforward
          (fun z => WholeArraySampler.childrenAt slots rows chosen z.1 z.2) := by
      apply congrArg (fun μ : FiniteDistribution
          (Arrays (childSlots slots chosen) rows ×
            ((child : RecursiveSampler.OffPath chosen) →
              Arrays (childSlots slots child.val) rows)) =>
        μ.pushforward (fun z => WholeArraySampler.childrenAt slots rows chosen z.1 z.2))
      apply FiniteDistribution.eq_of_weight_eq
      rintro ⟨a, b⟩
      simp only [WholeArraySampler.law, FiniteDistribution.pushforward,
        FiniteDistribution.product]
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : WholeArraySampler.evaluate rows repeats q
        (childSlots slots chosen) ω = a <;> simp [h]
    _ = _ := childrenAt_law rows slots chosen
      (fun child => WholeArraySampler.law rows repeats q (childSlots slots child))

theorem belowEvaluate_law (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    (OriginalWholeCutTape.belowLaw rows repeats chosen q slots).pushforward
        (OriginalWholeCut.belowEvaluate rows repeats chosen q slots) =
      belowArraysLaw rows repeats chosen q slots :=
  below_product_law rows repeats chosen q slots

def valuesLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (OriginalWholeCut.Values rows repeats p slots) :=
  FiniteProduct.law (fun _ : OriginalCutCalls.Index rows repeats p =>
    RecursiveSampler.law F2 repeats (.step chosen q)
      (LeafDomain (OriginalWholeCutTape.cutSlots p slots)))

theorem callsEvaluate_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (OriginalWholeCutTape.callsLaw rows repeats p chosen q slots).pushforward
        (fun calls call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
          (LeafDomain (OriginalWholeCutTape.cutSlots p slots)) (calls call)) =
      valuesLaw rows repeats p chosen q slots :=
  FiniteProduct.pushforward_map
    (fun _ : OriginalCutCalls.Index rows repeats p =>
      RecursiveSampler.tapeLaw F2 repeats (.step chosen q)
        (LeafDomain (OriginalWholeCutTape.cutSlots p slots)))
    (fun _ => RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain (OriginalWholeCutTape.cutSlots p slots)))

theorem numberedValues_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (valuesLaw rows repeats p chosen q slots).pushforward
        (OriginalWholeCut.numberedValues rows repeats p slots) =
      FiniteProduct.law (fun _ : Fin (OriginalCutCalls.count rows repeats n (m + 1)) =>
        RecursiveSampler.law F2 repeats (.step chosen q)
          (LeafDomain (OriginalWholeCutTape.cutSlots p slots))) := by
  change (valuesLaw rows repeats p chosen q slots).pushforward
    (Equiv.arrowCongr (OriginalWholeCut.callNumbering rows repeats p)
      (Equiv.refl (H (OriginalWholeCutTape.cutSlots p slots)))) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro values
  change (∏ call : OriginalCutCalls.Index rows repeats p,
      (RecursiveSampler.law F2 repeats (.step chosen q)
        (LeafDomain (OriginalWholeCutTape.cutSlots p slots))).weight
          (values (OriginalWholeCut.callNumbering rows repeats p call))) =
    ∏ call : Fin (OriginalCutCalls.count rows repeats n (m + 1)),
      (RecursiveSampler.law F2 repeats (.step chosen q)
        (LeafDomain (OriginalWholeCutTape.cutSlots p slots))).weight (values call)
  exact (OriginalWholeCut.callNumbering rows repeats p).prod_comp
    (fun call : Fin (OriginalCutCalls.count rows repeats n (m + 1)) =>
      (RecursiveSampler.law F2 repeats (.step chosen q)
        (LeafDomain (OriginalWholeCutTape.cutSlots p slots))).weight (values call))

def recordLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (OriginalWholeCut.Record rows repeats p slots) :=
  (OriginalWholeCutTape.exteriorLaw rows repeats p slots).product
    ((valuesLaw rows repeats p chosen q slots).product
      (belowArraysLaw rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots)))

theorem readRecord_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
        (OriginalWholeCut.readRecord rows repeats p chosen q slots) =
      recordLaw rows repeats p chosen q slots := by
  let values : OriginalWholeCutTape.Calls rows repeats p chosen q slots →
      OriginalWholeCut.Values rows repeats p slots :=
    fun calls call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain (OriginalWholeCutTape.cutSlots p slots)) (calls call)
  let arrays : OriginalWholeCutTape.BelowTape rows repeats chosen q
      (OriginalWholeCutTape.cutSlots p slots) → OriginalWholeCut.BelowArrays rows p slots :=
    OriginalWholeCut.belowEvaluate rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots)
  let observe : OriginalWholeCutTape.Exterior rows repeats p slots ×
      (OriginalWholeCutTape.Calls rows repeats p chosen q slots ×
        OriginalWholeCutTape.BelowTape rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots)) →
      OriginalWholeCut.Record rows repeats p slots :=
    fun z => (z.1, (values z.2.1, arrays z.2.2))
  change (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
    (fun ω => observe (OriginalWholeCutTape.splitTape rows repeats p chosen q slots ω)) = _
  rw [← FiniteDistribution.pushforward_comp
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots)
    (OriginalWholeCutTape.splitTape rows repeats p chosen q slots) observe,
    OriginalWholeCutTape.split_tapeLaw]
  apply Eq.trans (product_map_record
    (E := OriginalWholeCutTape.Exterior rows repeats p slots)
    (A := OriginalWholeCutTape.Calls rows repeats p chosen q slots)
    (B := OriginalWholeCutTape.BelowTape rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots))
    (V := OriginalWholeCut.Values rows repeats p slots)
    (D := OriginalWholeCut.BelowArrays rows p slots)
    (OriginalWholeCutTape.exteriorLaw rows repeats p slots)
    (OriginalWholeCutTape.callsLaw rows repeats p chosen q slots)
    (OriginalWholeCutTape.belowLaw rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots))
    values arrays)
  exact congrArg
    (fun μ : FiniteDistribution
        (OriginalWholeCut.Values rows repeats p slots × OriginalWholeCut.BelowArrays rows p slots) =>
      (OriginalWholeCutTape.exteriorLaw rows repeats p slots).product μ)
    (congrArg₂
      (fun (μ : FiniteDistribution (OriginalWholeCut.Values rows repeats p slots))
          (ν : FiniteDistribution (OriginalWholeCut.BelowArrays rows p slots)) => μ.product ν)
      (callsEvaluate_law rows repeats p chosen q slots)
      (belowEvaluate_law rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots)))

theorem reconstruct_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (recordLaw rows repeats p chosen q slots).pushforward
        (OriginalWholeCut.reconstructRecord rows repeats p slots) =
      WholeArraySampler.law rows repeats (p.append (.step chosen q)) slots := by
  calc
    _ = ((WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
        (OriginalWholeCut.readRecord rows repeats p chosen q slots)).pushforward
          (OriginalWholeCut.reconstructRecord rows repeats p slots) :=
      congrArg (fun μ : FiniteDistribution (OriginalWholeCut.Record rows repeats p slots) =>
        μ.pushforward (OriginalWholeCut.reconstructRecord rows repeats p slots))
          (readRecord_law rows repeats p chosen q slots).symm
    _ = (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
        (fun ω => OriginalWholeCut.reconstructRecord rows repeats p slots
          (OriginalWholeCut.readRecord rows repeats p chosen q slots ω)) :=
      FiniteDistribution.pushforward_comp _ _ _
    _ = _ := congrArg
      (fun f : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots →
          Arrays slots rows =>
        (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward f)
      (funext (fun ω => OriginalWholeCut.reconstruct_original rows repeats p chosen q slots ω))

end
end PerfectCompleteness.OriginalWholeCutLaw

end

end OAI
