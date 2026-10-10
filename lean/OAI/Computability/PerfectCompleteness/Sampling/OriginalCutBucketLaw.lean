import OAI.Computability.PerfectCompleteness.Construction.OriginalOwnBucketSplit
import OAI.Computability.PerfectCompleteness.Decoding.OriginalCutCollision

namespace OAI

section

namespace PerfectCompleteness.OriginalCutBucketLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

section Regrouping

private def reorder (D U B F : Type*) :
    D × ((U × B) × F) ≃ B × (D × (U × F)) where
  toFun z := (z.2.1.2, (z.1, (z.2.1.1, z.2.2)))
  invFun z := (z.2.1, ((z.2.2.1, z.1), z.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem reorder_law {D U B F : Type*}
    [Fintype D] [Fintype U] [Fintype B] [Fintype F]
    (directions : FiniteDistribution D) (own : FiniteDistribution U)
    (background : FiniteDistribution B) (fresh : FiniteDistribution F) :
    (directions.product ((own.product background).product fresh)).pushforward (reorder D U B F) =
      background.product (directions.product (own.product fresh)) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  change directions.weight z.2.1 *
      ((own.weight z.2.2.1 * background.weight z.1) * fresh.weight z.2.2.2) =
    background.weight z.1 *
      (directions.weight z.2.1 * (own.weight z.2.2.1 * fresh.weight z.2.2.2))
  ring

private theorem map_middle {D R S F : Type*}
    [Fintype D] [Fintype R] [Fintype S] [Fintype F]
    (directions : FiniteDistribution D) (records : FiniteDistribution R)
    (fresh : FiniteDistribution F) (read : R → S) :
    (directions.product (records.product fresh)).pushforward
        (fun z => (z.1, (read z.2.1, z.2.2))) =
      directions.product ((records.pushforward read).product fresh) := by
  have hinner : (records.product fresh).pushforward (fun z => (read z.1, z.2)) =
      (records.pushforward read).product fresh := by
    simpa only [id_eq, FiniteDistribution.pushforward_id] using
      FiniteDistribution.product_pushforward records fresh read (id : F → F)
  calc
    _ = (directions.pushforward id).product
        ((records.product fresh).pushforward (fun z => (read z.1, z.2))) :=
      FiniteDistribution.product_pushforward directions (records.product fresh) id
        (fun z => (read z.1, z.2))
    _ = _ := by rw [FiniteDistribution.pushforward_id, hinner]

private theorem read_product_of_split {D R U B F : Type*}
    [Fintype D] [Fintype R] [Fintype U] [Fintype B] [Fintype F]
    (directions : FiniteDistribution D) (records : FiniteDistribution R)
    (fresh : FiniteDistribution F) (own : FiniteDistribution U)
    (background : FiniteDistribution B) (split : R → U × B)
    (hsplit : records.pushforward split = own.product background) :
    (directions.product (records.product fresh)).pushforward
        (fun z => ((split z.2.1).2, (z.1, ((split z.2.1).1, z.2.2)))) =
      background.product (directions.product (own.product fresh)) := by
  calc
    _ = ((directions.product (records.product fresh)).pushforward
        (fun z => (z.1, (split z.2.1, z.2.2)))).pushforward (reorder D U B F) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (directions.product ((own.product background).product fresh)).pushforward
        (reorder D U B F) := by
      rw [map_middle, hsplit]
    _ = _ := reorder_law directions own background fresh

end Regrouping

variable {branch : Nat → Nat} {n m k t : Nat}

abbrev Background (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  HierarchicalMatrixTable.Background (rows := rows) slots (WholeArrayInteriorExterior.upperNode p)

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Background rows p slots) := Fintype.ofFinite _

abbrev NativeSample (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Background rows p slots ×
    (BucketSampler.Direction (rows (m + 1)) ×
      (OriginalOwnBucketSplit.BucketTape rows p slots × H (cutSlots p slots)))

def read (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (m + 1)) ×
      OriginalExtraCutComparison.Record rows repeats p slots) : NativeSample rows p slots :=
  (HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
      (OriginalCutCollision.oldArrays rows repeats p slots sample.2),
    (sample.1,
      (OriginalCutBucketReplacement.ownValues rows repeats p slots
        (OriginalCutCollision.oldRecord rows repeats p slots sample.2).2.1, sample.2.2)))

def recordRead (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats p slots) :
    OriginalOwnBucketSplit.BucketTape rows p slots × Background rows p slots :=
  ((OriginalOwnBucketSplit.recordEquiv rows repeats p slots record).1,
    HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
      (OriginalWholeCut.reconstructRecord rows repeats p slots record))

@[simp] theorem oldRecord_numberRecord (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats p slots) (fresh : H (cutSlots p slots)) :
    OriginalCutCollision.oldRecord rows repeats p slots
        (OriginalWholeCutBridge.numberRecord rows repeats p slots record, fresh) = record :=
  (NumberedUniformCut.numberRecordEquiv rows repeats p slots).symm_apply_apply record

theorem read_numberRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (direction : BucketSampler.Direction (rows (m + 1)))
    (record : OriginalWholeCut.Record rows repeats p slots) (fresh : H (cutSlots p slots)) :
    read rows repeats p slots
        (direction, (OriginalWholeCutBridge.numberRecord rows repeats p slots record, fresh)) =
      ((recordRead rows repeats p slots record).2,
        (direction, ((recordRead rows repeats p slots record).1, fresh))) := by
  unfold read OriginalCutCollision.oldArrays
  simp only [oldRecord_numberRecord]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext a
        exact (OriginalOwnBucketSplit.recordEquiv_own rows repeats p slots record a).symm
      · rfl

private theorem numbered_read_of_split (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (m + 1))))
    (records : FiniteDistribution (OriginalWholeCut.Record rows repeats p slots))
    (fresh : FiniteDistribution (H (cutSlots p slots)))
    (own : FiniteDistribution (OriginalOwnBucketSplit.BucketTape rows p slots))
    (background : FiniteDistribution (Background rows p slots))
    (hsplit : records.pushforward (recordRead rows repeats p slots) = own.product background) :
    (directions.product ((records.pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product fresh)).pushforward
          (read rows repeats p slots) =
      background.product (directions.product (own.product fresh)) := by
  calc
    _ = (directions.product (records.product fresh)).pushforward
        (fun z => read rows repeats p slots
          (z.1, (OriginalWholeCutBridge.numberRecord rows repeats p slots z.2.1, z.2.2))) := by
      rw [← map_middle directions records fresh
        (OriginalWholeCutBridge.numberRecord rows repeats p slots),
        FiniteDistribution.pushforward_comp]
    _ = (directions.product (records.product fresh)).pushforward
        (fun z => ((recordRead rows repeats p slots z.2.1).2,
          (z.1, ((recordRead rows repeats p slots z.2.1).1, z.2.2)))) := by
      apply congrArg (directions.product (records.product fresh)).pushforward
      funext z
      exact read_numberRecord rows repeats p slots z.1 z.2.1 z.2.2
    _ = _ := read_product_of_split directions records fresh own background
      (recordRead rows repeats p slots) hsplit

theorem reference_read_law (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (m + 1)))) :
    (directions.product (OriginalExtraCutComparison.referenceLaw rows repeats p slots)).pushforward
        (read rows repeats p slots) =
      (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots).product
        (directions.product
          ((FiniteDistribution.uniform (OriginalOwnBucketSplit.BucketTape rows p slots)).product
            (FiniteDistribution.uniform (H (cutSlots p slots))))) := by
  unfold OriginalExtraCutComparison.referenceLaw
  rw [OriginalUniformCut.referenceLaw_uniform]
  exact numbered_read_of_split rows repeats p slots directions
    (FiniteDistribution.uniform (OriginalWholeCut.Record rows repeats p slots))
    (FiniteDistribution.uniform (H (cutSlots p slots)))
    (FiniteDistribution.uniform (OriginalOwnBucketSplit.BucketTape rows p slots))
    (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots)
    (OriginalOwnBucketSplit.uniform_own_background rows repeats p slots)

theorem record_fresh_read_law (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (m + 1)))) :
    (directions.product
      (((OriginalWholeCutLaw.recordLaw rows repeats p chosen q slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product
          (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))))).pushforward
      (read rows repeats p slots) =
      (OriginalOwnBucketSplit.actualBackgroundLaw rows repeats p chosen q slots).product
        (directions.product
          ((BucketSampler.tapeLaw (rows (m + 1))
            (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))).product
              (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))))) :=
  numbered_read_of_split rows repeats p slots directions
    (OriginalWholeCutLaw.recordLaw rows repeats p chosen q slots)
    (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))
    (BucketSampler.tapeLaw (rows (m + 1))
      (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))))
    (OriginalOwnBucketSplit.actualBackgroundLaw rows repeats p chosen q slots)
    (OriginalOwnBucketSplit.recordLaw_own_background rows repeats p chosen q slots)

end
end PerfectCompleteness.OriginalCutBucketLaw

end

end OAI
