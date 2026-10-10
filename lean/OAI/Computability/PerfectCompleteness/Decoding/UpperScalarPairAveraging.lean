import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutErasure
import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarFreshProjectionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas

namespace OAI

section

namespace PerfectCompleteness.UpperScalarPairAveraging

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] linearMapFintype

private theorem map_right {D A B Γ : Type*}
    [Fintype D] [Fintype A] [Fintype B] [Fintype Γ]
    (δ : FiniteDistribution D) (μ : FiniteDistribution A)
    (f : A → B) (g : D × B → Γ) :
    (δ.product (μ.pushforward f)).pushforward g =
      (δ.product μ).pushforward (fun z => g (z.1, f z.2)) := by
  have h := FiniteDistribution.product_pushforward δ μ id f
  simp only [FiniteDistribution.pushforward_id, id_eq] at h
  rw [← h, FiniteDistribution.pushforward_comp]

private theorem map_three {D A B A' B' Γ : Type*}
    [Fintype D] [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype Γ]
    (δ : FiniteDistribution D) (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (f : A → A') (g : B → B') (observe : D × (A' × B') → Γ) :
    (δ.product ((μ.pushforward f).product (ν.pushforward g))).pushforward observe =
      (δ.product (μ.product ν)).pushforward
        (fun z => observe (z.1, (f z.2.1, g z.2.2))) := by
  rw [← FiniteDistribution.product_pushforward μ ν f g]
  exact map_right δ (μ.product ν) (fun z => (f z.1, g z.2)) observe

private theorem product_mixture {E A B : Type*}
    [Fintype E] [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (κ : FiniteDistribution E)
    (ν : E → FiniteDistribution B) :
    μ.product (κ.mixture ν) = κ.mixture (fun e => μ.product (ν e)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.product, FiniteDistribution.mixture, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact mul_left_comm _ _ _

variable {branch : Nat → Nat} {n j i k t : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

private theorem tapeLaw_cast (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {u v : Path branch n k} (h : u = v) :
    (WholeArraySampler.tapeLaw rows repeats u slots).pushforward
        (Equiv.cast (congrArg (fun path => WholeArraySampler.Tape rows repeats path slots) h)) =
      WholeArraySampler.tapeLaw rows repeats v slots := by
  cases h
  change (WholeArraySampler.tapeLaw rows repeats u slots).pushforward id = _
  exact FiniteDistribution.pushforward_id _

theorem assocTapeEquiv_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats ((p.append r).append q) slots).pushforward
        (UpperScalarCutErasure.assocTapeEquiv rows repeats p r q slots) =
      WholeArraySampler.tapeLaw rows repeats (p.append (r.append q)) slots :=
  tapeLaw_cast rows repeats slots (p.append_assoc r q)

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

def pathPairLaw (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    Path branch (j + 1) 0 →
      FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p))
  | .step chosen q =>
      (directions.product
        (((OriginalWholeCutLaw.recordLaw rows repeats p chosen q slots).pushforward
          (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product
            (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))))).pushforward
          (OriginalCutCollision.pairRecord rows repeats p slots)

private theorem upper_step_tape_law (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (chosen : Fin (branch j)) (q : Path branch j 0)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    (directions.product
      ((WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).product
        (RecursiveSampler.tapeLaw F2 repeats (.step chosen q)
          (LeafDomain (cutSlots p slots))))).pushforward
      (fun z => OriginalCutCollision.pairRecord rows repeats p slots
        (z.1, (OriginalWholeCutBridge.numberRecord rows repeats p slots
          (OriginalWholeCut.readRecord rows repeats p chosen q slots z.2.1),
          RecursiveSampler.evaluate F2 repeats (.step chosen q)
            (LeafDomain (cutSlots p slots)) z.2.2))) =
      pathPairLaw rows repeats p slots directions (.step chosen q) := by
  let : Fintype (OriginalWholeCut.Values rows repeats p slots ×
      OriginalWholeCut.BelowArrays rows p slots) :=
    OriginalWholeCutLaw.valuesBelowFintype rows repeats p slots
  rw [← map_three directions
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots)
    (RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))
    (fun tape => OriginalWholeCutBridge.numberRecord rows repeats p slots
      (OriginalWholeCut.readRecord rows repeats p chosen q slots tape))
    (RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))
    (OriginalCutCollision.pairRecord rows repeats p slots)]
  rw [← FiniteDistribution.pushforward_comp
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots)
    (OriginalWholeCut.readRecord rows repeats p chosen q slots)
    (OriginalWholeCutBridge.numberRecord rows repeats p slots),
    OriginalWholeCutLaw.readRecord_law]
  rfl

private theorem upper_read_law (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (chosen : Fin (branch i)) (q : Path branch i 0)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    (directions.product
      ((WholeArraySampler.tapeLaw rows repeats (p.append (r.append (.step chosen q))) slots).product
        (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots))))).pushforward
      (fun z => UpperScalarCutErasure.upperPairRecord rows repeats p r chosen q slots z.2.1 z.1
        (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots)) z.2.2)) =
      pathPairLaw rows repeats p slots directions (r.append (.step chosen q)) := by
  cases r with
  | refl => exact upper_step_tape_law rows repeats p chosen q slots directions
  | step upperChild tail =>
      exact upper_step_tape_law rows repeats p upperChild (tail.append (.step chosen q)) slots directions

theorem fixed_pairLaw (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (chosen : Fin (branch i)) (q : Path branch i 0)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    UpperScalarPairComparison.pairLaw rows repeats p r slots directions
      ((OriginalChildBlocks.sourceLaw (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1))
        rows repeats chosen q (cutSlots (p.append r) slots)).pushforward
          (OriginalChildBlocks.observed (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1))
            rows repeats chosen q (cutSlots (p.append r) slots))) =
      pathPairLaw rows repeats p slots directions (r.append (.step chosen q)) := by
  let oldTape := WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots
  let freshTape := RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
    (LeafDomain (cutSlots p slots))
  let observe := fun z : BucketSampler.Direction (rows (j + 1)) ×
      (WholeArraySampler.Tape rows repeats (p.append (r.append (.step chosen q))) slots ×
        RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) =>
    UpperScalarCutErasure.upperPairRecord rows repeats p r chosen q slots z.2.1 z.1
      (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots)) z.2.2)
  unfold UpperScalarPairComparison.pairLaw
  rw [← UpperScalarCutLaw.numbered_read_law rows repeats p r chosen q slots, map_right]
  have hmap :
      (fun z : BucketSampler.Direction (rows (j + 1)) ×
        (WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
          RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) =>
        UpperScalarCutBucket.numberedPairRecord rows repeats p r slots
          (z.1, UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r slots
            (UpperScalarCutReconstruction.read rows repeats p r chosen q slots z.2))) =
        (fun z => observe (z.1,
          (UpperScalarCutErasure.assocTapeEquiv rows repeats p r (.step chosen q) slots z.2.1,
            id z.2.2))) := by
    funext z
    exact UpperScalarCutErasure.numberedPairRecord_read_eq_upper
      rows repeats p r chosen q slots z.1 z.2
  rw [hmap, ← map_three directions oldTape freshTape
    (UpperScalarCutErasure.assocTapeEquiv rows repeats p r (.step chosen q) slots) id observe]
  dsimp only [oldTape]
  rw [assocTapeEquiv_law, FiniteDistribution.pushforward_id]
  exact upper_read_law rows repeats p r chosen q slots directions

theorem continued_pairLaw_eq_mixture {K : Type*} [Fintype K]
    (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (ν : FiniteDistribution K) (q : K → Path branch i 0) (hbranch : 0 < branch i) :
    UpperScalarPairComparison.pairLaw rows repeats p r slots directions
      (OriginalPrefixContinuation.assembledLaw
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows repeats
        (cutSlots (p.append r) slots) ν q hbranch) =
      (OriginalPrefixContinuation.tagLaw ν hbranch).mixture
        (fun tag => pathPairLaw rows repeats p slots directions (r.append (.step tag.1 (q tag.2)))) := by
  unfold UpperScalarPairComparison.pairLaw
  rw [OriginalPrefixContinuation.assembledLaw_eq_mixture, product_mixture,
    product_mixture, FiniteDistribution.pushforward_mixture]
  apply congrArg ((OriginalPrefixContinuation.tagLaw ν hbranch).mixture)
  funext tag
  exact fixed_pairLaw rows repeats p r tag.1 (q tag.2) slots directions

private theorem geometric_tagLaw (m : Nat) (hbranch : ∀ k < m + 1, 0 < branch k) :
    OriginalPrefixContinuation.tagLaw
      (GeometricPath.law m (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self m))))
      (hbranch m (Nat.lt_succ_self m)) = GeometricPath.law (m + 1) hbranch :=
  (GeometricPath.law_step m hbranch).symm

theorem lower_geometric_pairLaw (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (hbranch : ∀ k < i + 1, 0 < branch k) :
    UpperScalarPairComparison.pairLaw rows repeats p r slots directions
      (OriginalPrefixContinuation.assembledLaw
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows repeats
        (cutSlots (p.append r) slots)
        (GeometricPath.law i (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self i))))
        GeometricPath.leafPath (hbranch i (Nat.lt_succ_self i))) =
      (GeometricPath.law (i + 1) hbranch).mixture
        (fun leaf => pathPairLaw rows repeats p slots directions (r.append (GeometricPath.leafPath leaf))) := by
  rw [continued_pairLaw_eq_mixture, geometric_tagLaw]
  rfl

theorem upper_geometric_pairLaw (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (hbranch : ∀ k < j + 1, 0 < branch k) :
    (directions.product (OriginalExtraCutComparison.actualLaw rows repeats p slots
      (GeometricPath.law j (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self j))))
      GeometricPath.leafPath (hbranch j (Nat.lt_succ_self j)))).pushforward
        (OriginalCutCollision.pairRecord rows repeats p slots) =
      (GeometricPath.law (j + 1) hbranch).mixture
        (fun leaf => pathPairLaw rows repeats p slots directions (GeometricPath.leafPath leaf)) := by
  rw [OriginalExtraCutComparison.actualLaw_eq_mixture, product_mixture,
    FiniteDistribution.pushforward_mixture, geometric_tagLaw]
  rfl

theorem geometric_average_eq_actual (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (hcut : i + 1 ≤ j + 1)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (hbranch : ∀ k < j + 1, 0 < branch k) :
    (GeometricCutSplit.prefixLaw hcut hbranch).mixture (fun pref =>
      UpperScalarPairComparison.pairLaw rows repeats p (GeometricCutSplit.prefixPath hcut pref)
        slots directions
        (OriginalPrefixContinuation.assembledLaw
          (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows repeats
          (cutSlots (p.append (GeometricCutSplit.prefixPath hcut pref)) slots)
          (GeometricPath.law i (fun k hk =>
            hbranch k (Nat.lt_of_lt_of_le (Nat.lt_trans hk (Nat.lt_succ_self i)) hcut)))
          GeometricPath.leafPath
          (hbranch i (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hcut)))) =
      (directions.product (OriginalExtraCutComparison.actualLaw rows repeats p slots
        (GeometricPath.law j (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self j))))
        GeometricPath.leafPath (hbranch j (Nat.lt_succ_self j)))).pushforward
          (OriginalCutCollision.pairRecord rows repeats p slots) := by
  rw [upper_geometric_pairLaw]
  rw [GeometricCutMixture.path_mixture_split hcut hbranch]
  apply congrArg ((GeometricCutSplit.prefixLaw hcut hbranch).mixture)
  funext pref
  exact lower_geometric_pairLaw rows repeats p (GeometricCutSplit.prefixPath hcut pref)
    slots directions (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))

end
end PerfectCompleteness.UpperScalarPairAveraging

end

end OAI
