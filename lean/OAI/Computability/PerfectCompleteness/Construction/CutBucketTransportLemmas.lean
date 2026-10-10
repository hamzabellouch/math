import OAI.Computability.PerfectCompleteness.Construction.CutNodeRows
import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalUsefulCollision
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAgreementMean

namespace OAI

section

namespace PerfectCompleteness.CutBucketTransport

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n m t : Nat}

local instance rowSpaceFintype (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

def nativeLaw (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (hrows : 0 < rows (m + 1)) :
    FiniteDistribution (BucketSampler.Direction (rows (m + 1)) ×
      (BucketSampler.Tape (rows (m + 1)) (H (cutSlots p slots)) × H (cutSlots p slots))) := by
  letI : Nonempty (BucketSampler.Direction (rows (m + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).product
    ((BucketSampler.tapeLaw (rows (m + 1))
      (FiniteDistribution.uniform (H (cutSlots p slots)))).product
        (FiniteDistribution.uniform (H (cutSlots p slots))))

theorem nativeLaw_pushforward (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (hrows : 0 < rows (m + 1)) :
    (nativeLaw rows p slots hrows).pushforward (CutNodeRows.bucketSampleEquiv rows p slots) =
      HierarchicalAgreementMean.bucketLaw slots (upperNode p)
        (by simpa only [upperNode_height] using hrows) := by
  let : Nonempty (BucketSampler.Direction (rows (m + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  let : Nonempty (BucketSampler.Direction (rows (Nodes.height (upperNode p)))) :=
    ⟨CutNodeRows.directionEquiv rows p (BucketUniform.coordinateDirection ⟨0, hrows⟩)⟩
  unfold nativeLaw HierarchicalAgreementMean.bucketLaw
  simp only [BucketSampler.tapeLaw, UniformLinearImage.law_uniform,
    WholeCutSampler.uniform_product]
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (CutNodeRows.bucketSampleEquiv rows p slots)

end
end PerfectCompleteness.CutBucketTransport

end

section

namespace PerfectCompleteness.CutBucketTransportActual

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

local instance rowSpaceFintype (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

theorem tapeLaw_pushforward (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (scalar : FiniteDistribution (H (cutSlots p slots))) :
    (BucketSampler.tapeLaw (rows (m + 1)) scalar).pushforward
        (CutNodeRows.bucketTapeEquiv rows p slots) =
      BucketSampler.tapeLaw (rows (Nodes.height (upperNode p)))
        (scalar.pushforward (CutNodeRows.cutRowEquiv p slots)) := by
  have hscalar := FiniteDistribution.transport_eq_pushforward scalar
    (CutNodeRows.cutRowEquiv p slots).toEquiv
  change scalar.transport (CutNodeRows.cutRowEquiv p slots).toEquiv =
    scalar.pushforward (CutNodeRows.cutRowEquiv p slots) at hscalar
  rw [← FiniteDistribution.transport_eq_pushforward
      (BucketSampler.tapeLaw (rows (m + 1)) scalar) (CutNodeRows.bucketTapeEquiv rows p slots),
    ← hscalar]
  apply FiniteDistribution.eq_of_weight_eq
  intro tape
  change (∏ a : BucketSampler.Direction (rows (m + 1)),
      scalar.weight ((CutNodeRows.cutRowEquiv p slots).symm
        (tape (CutNodeRows.directionEquiv rows p a)))) =
    ∏ a : BucketSampler.Direction (rows (Nodes.height (upperNode p))),
      scalar.weight ((CutNodeRows.cutRowEquiv p slots).symm (tape a))
  exact (CutNodeRows.directionEquiv rows p).prod_comp (M := ℝ)
    (fun a : BucketSampler.Direction (rows (Nodes.height (upperNode p))) =>
      scalar.weight ((CutNodeRows.cutRowEquiv p slots).symm (tape a)))

theorem bucketSampleLaw_pushforward (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (m + 1))))
    (scalar : FiniteDistribution (H (cutSlots p slots))) :
    (directions.product ((BucketSampler.tapeLaw (rows (m + 1)) scalar).product scalar)).pushforward
        (CutNodeRows.bucketSampleEquiv rows p slots) =
      (directions.pushforward (CutNodeRows.directionEquiv rows p)).product
        ((BucketSampler.tapeLaw (rows (Nodes.height (upperNode p)))
          (scalar.pushforward (CutNodeRows.cutRowEquiv p slots))).product
            (scalar.pushforward (CutNodeRows.cutRowEquiv p slots))) := by
  change (directions.product
      ((BucketSampler.tapeLaw (rows (m + 1)) scalar).product scalar)).pushforward
        (fun z => (CutNodeRows.directionEquiv rows p z.1,
          (CutNodeRows.bucketTapeEquiv rows p slots z.2.1,
            CutNodeRows.cutRowEquiv p slots z.2.2))) = _
  rw [FiniteDistribution.product_pushforward directions
    ((BucketSampler.tapeLaw (rows (m + 1)) scalar).product scalar)
    (CutNodeRows.directionEquiv rows p)
    (fun z => (CutNodeRows.bucketTapeEquiv rows p slots z.1,
      CutNodeRows.cutRowEquiv p slots z.2))]
  rw [FiniteDistribution.product_pushforward
    (BucketSampler.tapeLaw (rows (m + 1)) scalar) scalar
    (CutNodeRows.bucketTapeEquiv rows p slots) (CutNodeRows.cutRowEquiv p slots),
    tapeLaw_pushforward]

def nativeLaw (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (scalar : FiniteDistribution (H (cutSlots p slots))) (hrows : 0 < rows (m + 1)) :
    FiniteDistribution (BucketSampler.Direction (rows (m + 1)) ×
      (BucketSampler.Tape (rows (m + 1)) (H (cutSlots p slots)) × H (cutSlots p slots))) := by
  letI : Nonempty (BucketSampler.Direction (rows (m + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).product
    ((BucketSampler.tapeLaw (rows (m + 1)) scalar).product scalar)

theorem nativeLaw_pushforward (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (scalar : FiniteDistribution (H (cutSlots p slots))) (hrows : 0 < rows (m + 1)) :
    (nativeLaw rows p slots scalar hrows).pushforward (CutNodeRows.bucketSampleEquiv rows p slots) =
      HierarchicalUsefulCollision.bucketLaw slots (upperNode p)
        (scalar.pushforward (CutNodeRows.cutRowEquiv p slots))
        (by simpa only [upperNode_height] using hrows) := by
  let : Nonempty (BucketSampler.Direction (rows (m + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  let : Nonempty (BucketSampler.Direction (rows (Nodes.height (upperNode p)))) :=
    ⟨CutNodeRows.directionEquiv rows p (BucketUniform.coordinateDirection ⟨0, hrows⟩)⟩
  have hdirections :
      (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).pushforward
          (CutNodeRows.directionEquiv rows p) =
        HierarchicalUsefulCollision.directionLaw (rows := rows) (upperNode p)
          (by simpa only [upperNode_height] using hrows) := by
    change (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).pushforward
      (CutNodeRows.directionEquiv rows p) =
        FiniteDistribution.uniform (BucketSampler.Direction (rows (Nodes.height (upperNode p))))
    rw [← FiniteDistribution.transport_eq_pushforward]
    exact UniformConditioning.uniform_transport (CutNodeRows.directionEquiv rows p)
  unfold nativeLaw HierarchicalUsefulCollision.bucketLaw
  rw [bucketSampleLaw_pushforward, hdirections]

end
end PerfectCompleteness.CutBucketTransportActual

end

end OAI
