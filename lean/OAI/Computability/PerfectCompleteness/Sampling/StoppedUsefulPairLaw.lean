import OAI.Computability.PerfectCompleteness.Construction.CutBucketTransportLemmas
import OAI.Computability.PerfectCompleteness.Construction.StoppedBucketRows
import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutProjection
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.BucketDescriptorLaw
import OAI.Computability.PerfectCompleteness.Sampling.WholeArrayBucketsLaw

namespace OAI

section

namespace PerfectCompleteness.StoppedUsefulPairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {N j i t : Nat}

abbrev Descriptor (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (right : Slots branch N → Fin t → MixedSupport.Slot) :=
  WholeArrayInteriorHiddenLaw.Exterior rows repeats p chosen q right

def externalLaw (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (right : Slots branch N → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Descriptor rows repeats p chosen q right) :=
  WholeArrayInteriorHiddenLaw.exteriorLaw rows repeats p chosen q right

local instance rowSpaceFintype (p : Path branch N (j + 1))
    (native : Slots branch N → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace native (upperNode p)) := Fintype.ofFinite _

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch N (j + 1))
    (native : Slots branch N → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) native (upperNode p)) :=
  Fintype.ofFinite _

def background (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (external : Descriptor rows repeats p chosen q right) :
    HierarchicalMatrixTable.Background (rows := rows) native (upperNode p) :=
  fun node row => HPullback (ChildBlockProjection.nodeProjection projection node.val)
    (WholeArrayInteriorExterior.nodeArray rows repeats p chosen q right external node row)

def scalarValue (repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (tape : WholeArrayInteriorHiddenLaw.ScalarTape repeats p chosen q right) :
    H (cutSlots p native) :=
  HPullback (CutGroupedProjection.cutProjection p projection)
    (RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain (cutSlots p right)) tape)

def nativeScalarLaw (repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a)) :
    FiniteDistribution (H (cutSlots p native)) :=
  (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p right))).pushforward
    (HPullback (CutGroupedProjection.cutProjection p projection))

def scalarLaw (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (_external : Descriptor rows repeats p chosen q right) :
    FiniteDistribution (NodeEmbedding.RowSpace native (upperNode p)) :=
  (nativeScalarLaw repeats p chosen q native right projection).pushforward
    (CutNodeRows.cutRowEquiv p native)

def readout (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a)) :=
  WholeArrayBucketsLaw.readout rows repeats p chosen q right
    (scalarValue repeats p chosen q native right projection)
    (id : Descriptor rows repeats p chosen q right → _)

theorem scalarValue_law (repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a)) :
    (WholeArrayInteriorHiddenLaw.scalarLaw repeats p chosen q right).pushforward
        (scalarValue repeats p chosen q native right projection) =
      nativeScalarLaw repeats p chosen q native right projection := by
  exact (FiniteDistribution.pushforward_comp
    (RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain (cutSlots p right)))
    (RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain (cutSlots p right)))
    (HPullback (CutGroupedProjection.cutProjection p projection))).symm

theorem readout_law (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a)) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right).pushforward
        (readout rows repeats p chosen q native right projection) =
      (externalLaw rows repeats p chosen q right).product
        (BucketSampler.tapeLaw (rows (j + 1))
          (nativeScalarLaw repeats p chosen q native right projection)) := by
  rw [readout, WholeArrayBucketsLaw.readout_law,
    FiniteDistribution.pushforward_id, scalarValue_law]
  rfl

theorem background_readout (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right) :
    background rows repeats p chosen q native right projection
        (readout rows repeats p chosen q native right projection tape).1 =
      HierarchicalMatrixTable.backgroundOf native (upperNode p)
        (ChildBlockProjection.arraysPullback rows projection
          (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) right tape)) := by
  funext node row
  change HPullback (ChildBlockProjection.nodeProjection projection node.val)
    (WholeArrayInteriorExterior.nodeArray rows repeats p chosen q right
      (WholeArrayInteriorExterior.read rows repeats p chosen q right tape) node row) = _
  rw [WholeArrayInteriorExterior.nodeArray_read]
  rfl

theorem matrix_readout (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right) :
    NodeEmbedding.matrix (ChildBlockProjection.arraysPullback rows projection
        (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) right tape))
        (upperNode p) =
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace native (upperNode p))
        (rows (Nodes.height (upperNode p)))
        (CutNodeRows.bucketTapeEquiv rows p native
          (readout rows repeats p chosen q native right projection tape).2) := by
  rw [← CutNodeRows.matrixOfRows_selectedRows rows p native]
  have hrows := StoppedBucketRows.selectedRows_pullback_evaluate rows repeats p chosen q
    native right projection tape
  change SelectedArrayReplacement.selectedRows rows p native
      (ChildBlockProjection.arraysPullback rows projection
        (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) right tape)) =
    BucketSampler.evaluate (rows (j + 1)) id
      (readout rows repeats p chosen q native right projection tape).2 at hrows
  rw [hrows]
  exact CutNodeRows.matrixOfRows_evaluate rows p native _

theorem assembled_arrays (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right) :
    HierarchicalMatrixTable.assemble native (upperNode p)
        (background rows repeats p chosen q native right projection
          (readout rows repeats p chosen q native right projection tape).1)
        (BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace native (upperNode p))
          (rows (Nodes.height (upperNode p)))
          (CutNodeRows.bucketTapeEquiv rows p native
            (readout rows repeats p chosen q native right projection tape).2)) =
      ChildBlockProjection.arraysPullback rows projection
        (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) right tape) := by
  rw [background_readout, ← matrix_readout]
  exact HierarchicalMatrixTable.assemble_original native (upperNode p) _

abbrev Sample (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (right : Slots branch N → Fin t → MixedSupport.Slot) :=
  BucketSampler.Direction (rows (j + 1)) ×
    (WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right × H (cutSlots p right))

def directionLaw (rows : Nat → Nat) (j : Nat) (hrows : 0 < rows (j + 1)) :
    FiniteDistribution (BucketSampler.Direction (rows (j + 1))) := by
  letI : Nonempty (BucketSampler.Direction (rows (j + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact FiniteDistribution.uniform _

def actualLaw (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (right : Slots branch N → Fin t → MixedSupport.Slot) (hrows : 0 < rows (j + 1)) :
    FiniteDistribution (Sample rows repeats p chosen q right) :=
  (directionLaw rows j hrows).product
    ((WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right).product
      (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p right))))

def observe (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (sample : Sample rows repeats p chosen q right) :
    HierarchicalUsefulCollision.Sample (P := Descriptor rows repeats p chosen q right)
      (rows := rows) native (upperNode p) :=
  let old := readout rows repeats p chosen q native right projection sample.2.1
  ⟨old.1, CutNodeRows.bucketSampleEquiv rows p native
    (sample.1, (old.2, HPullback (CutGroupedProjection.cutProjection p projection) sample.2.2))⟩

private def liftFresh (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (sample : Sample rows repeats p chosen q right) :
    BucketSampler.Direction (rows (j + 1)) ×
      (WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right × H (cutSlots p native)) :=
  (sample.1, (sample.2.1, HPullback (CutGroupedProjection.cutProjection p projection) sample.2.2))

private theorem liftFresh_law (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (hrows : 0 < rows (j + 1)) :
    (actualLaw rows repeats p chosen q right hrows).pushforward
        (liftFresh rows repeats p chosen q native right projection) =
      (directionLaw rows j hrows).product
        ((WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right).product
          (nativeScalarLaw repeats p chosen q native right projection)) := by
  let μ := WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right
  let ρ := RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p right))
  let f := HPullback (CutGroupedProjection.cutProjection p projection)
  change ((directionLaw rows j hrows).product (μ.product ρ)).pushforward
    (fun z => (id z.1, (id z.2.1, f z.2.2))) = _
  rw [FiniteDistribution.product_pushforward (directionLaw rows j hrows) (μ.product ρ)
    id (fun z => (id z.1, f z.2)), FiniteDistribution.pushforward_id,
    FiniteDistribution.product_pushforward μ ρ id f, FiniteDistribution.pushforward_id]
  rfl

private theorem descriptor_chain_law
    {S D E T B V U : Type*}
    [Fintype S] [Fintype D] [Fintype E] [Fintype T]
    [Fintype B] [Fintype V] [Fintype U]
    (μ : FiniteDistribution S) (δ : FiniteDistribution D)
    (τ : FiniteDistribution T) (ν : FiniteDistribution E)
    (β : FiniteDistribution B) (ρ : FiniteDistribution V)
    (κ : FiniteDistribution U)
    (lift : S → D × (T × V))
    (read : T → E × B)
    (transport : D × (B × V) → U)
    (hLift : μ.pushforward lift = δ.product (τ.product ρ))
    (hRead : τ.pushforward read = ν.product β)
    (hTransport : (δ.product (β.product ρ)).pushforward transport = κ) :
    μ.pushforward (fun s =>
      (⟨(read (lift s).2.1).1,
        transport ((lift s).1, ((read (lift s).2.1).2, (lift s).2.2))⟩ : Σ _ : E, U)) =
      CompletionSoundness.sigmaLaw ν (fun _ => κ) := by
  let f : D × (T × V) → D × ((E × B) × V) :=
    fun z => (z.1, (read z.2.1, z.2.2))
  let r : D × ((E × B) × V) → (Σ _ : E, D × (B × V)) :=
    fun z => ⟨z.2.1.1, (z.1, (z.2.1.2, z.2.2))⟩
  let g : (Σ _ : E, D × (B × V)) → (Σ _ : E, U) :=
    fun z => ⟨z.1, transport z.2⟩
  have hInner : (τ.product ρ).pushforward
      (fun z : T × V => (read z.1, z.2)) = (ν.product β).product ρ := by
    simpa only [id_eq, FiniteDistribution.pushforward_id, hRead] using
      FiniteDistribution.product_pushforward τ ρ read (id : V → V)
  have hMap : (δ.product (τ.product ρ)).pushforward f =
      δ.product ((ν.product β).product ρ) := by
    simpa only [f, id_eq, FiniteDistribution.pushforward_id, hInner] using
      FiniteDistribution.product_pushforward δ (τ.product ρ) (id : D → D)
        (fun z : T × V => (read z.1, z.2))
  have hNative : ((μ.pushforward lift).pushforward f).pushforward r =
      CompletionSoundness.sigmaLaw ν (fun _ => δ.product (β.product ρ)) := by
    rw [hLift, hMap]
    exact BucketDescriptorLaw.reorder_law δ ν β ρ
  have hSigma :
      (CompletionSoundness.sigmaLaw ν (fun _ => δ.product (β.product ρ))).pushforward g =
      CompletionSoundness.sigmaLaw ν (fun _ => κ) := by
    calc
      _ = CompletionSoundness.sigmaLaw ν
          (fun _ => (δ.product (β.product ρ)).pushforward transport) :=
        SigmaObservation.pushforward_fiber ν
          (fun _ => δ.product (β.product ρ)) (fun _ => transport)
      _ = _ := congrArg
        (fun laws : E → FiniteDistribution U => CompletionSoundness.sigmaLaw ν laws)
        (funext (fun _ => hTransport))
  calc
    _ = (((μ.pushforward lift).pushforward f).pushforward r).pushforward g :=
      ((FiniteDistribution.pushforward_comp ((μ.pushforward lift).pushforward f) r g).trans
        ((FiniteDistribution.pushforward_comp (μ.pushforward lift) f
          (fun z : D × ((E × B) × V) => g (r z))).trans
          (FiniteDistribution.pushforward_comp μ lift
            (fun z : D × (T × V) => g (r (f z)))))).symm
    _ = (CompletionSoundness.sigmaLaw ν
        (fun _ => δ.product (β.product ρ))).pushforward g :=
      congrArg (fun law : FiniteDistribution (Σ _ : E, D × (B × V)) =>
        law.pushforward g) hNative
    _ = _ := hSigma

theorem observe_law (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (hrows : 0 < rows (j + 1)) :
    (actualLaw rows repeats p chosen q right hrows).pushforward
        (observe rows repeats p chosen q native right projection) =
      HierarchicalUsefulCollision.law native (upperNode p)
        (externalLaw rows repeats p chosen q right)
        (scalarLaw rows repeats p chosen q native right projection)
        (by simpa only [upperNode_height] using hrows) := by
  have h := descriptor_chain_law
    (S := Sample rows repeats p chosen q right)
    (D := BucketSampler.Direction (rows (j + 1)))
    (E := Descriptor rows repeats p chosen q right)
    (T := WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right)
    (B := BucketSampler.Tape (rows (j + 1)) (H (cutSlots p native)))
    (V := H (cutSlots p native))
    (U := HierarchicalAgreementMean.BucketSample (rows := rows) native (upperNode p))
    (actualLaw rows repeats p chosen q right hrows)
    (directionLaw rows j hrows)
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right)
    (externalLaw rows repeats p chosen q right)
    (BucketSampler.tapeLaw (rows (j + 1))
      (nativeScalarLaw repeats p chosen q native right projection))
    (nativeScalarLaw repeats p chosen q native right projection)
    (HierarchicalUsefulCollision.bucketLaw native (upperNode p)
      ((nativeScalarLaw repeats p chosen q native right projection).pushforward
        (CutNodeRows.cutRowEquiv p native))
      (by simpa only [upperNode_height] using hrows))
    (liftFresh rows repeats p chosen q native right projection)
    (readout rows repeats p chosen q native right projection)
    (CutNodeRows.bucketSampleEquiv rows p native)
    (liftFresh_law rows repeats p chosen q native right projection hrows)
    (readout_law rows repeats p chosen q native right projection)
    (CutBucketTransportActual.nativeLaw_pushforward rows p native
      (nativeScalarLaw repeats p chosen q native right projection) hrows)
  have hmap : observe rows repeats p chosen q native right projection =
      (fun s : Sample rows repeats p chosen q right =>
        (⟨(readout rows repeats p chosen q native right projection
              (liftFresh rows repeats p chosen q native right projection s).2.1).1,
          CutNodeRows.bucketSampleEquiv rows p native
            ((liftFresh rows repeats p chosen q native right projection s).1,
              ((readout rows repeats p chosen q native right projection
                (liftFresh rows repeats p chosen q native right projection s).2.1).2,
                (liftFresh rows repeats p chosen q native right projection s).2.2))⟩ :
          HierarchicalUsefulCollision.Sample (P := Descriptor rows repeats p chosen q right)
            (rows := rows) native (upperNode p))) := by
    funext s
    rfl
  exact (congrArg (fun f : Sample rows repeats p chosen q right →
      HierarchicalUsefulCollision.Sample (P := Descriptor rows repeats p chosen q right)
        (rows := rows) native (upperNode p) =>
      (actualLaw rows repeats p chosen q right hrows).pushforward f) hmap).trans h

theorem replacement_matrix (rows : Nat → Nat) (p : Path branch N (j + 1))
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (arrays : Arrays right rows)
    (buckets : BucketSampler.Tape (rows (j + 1)) (H (cutSlots p right)))
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p right)) :
    NodeEmbedding.matrix (ChildBlockProjection.arraysPullback rows projection
        (SelectedArrayReplacement.replace rows p right arrays
          (BucketSampler.evaluate (rows (j + 1)) id (Function.update buckets a fresh))))
        (upperNode p) =
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace native (upperNode p))
        (rows (Nodes.height (upperNode p)))
        (Function.update (CutNodeRows.bucketTapeEquiv rows p native
          (fun direction => HPullback (CutGroupedProjection.cutProjection p projection)
            (buckets direction))) (CutNodeRows.directionEquiv rows p a)
          (CutNodeRows.cutRowEquiv p native
            (HPullback (CutGroupedProjection.cutProjection p projection) fresh))) := by
  rw [← SelectedArrayProjection.replace_pullback rows p native right projection]
  rw [← CutNodeRows.matrixOfRows_selectedRows rows p native,
    SelectedArrayReplacement.selectedRows_replace]
  rw [← UpperScalarCutProjection.map_updated_buckets
    (HPullback (CutGroupedProjection.cutProjection p projection)) buckets a fresh]
  rw [CutNodeRows.matrixOfRows_evaluate, CutNodeRows.bucketTapeEquiv_update]

def actualPair (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (sample : Sample rows repeats p chosen q right) :
    HierarchicalAgreementMean.PairRecord (rows := rows) native (upperNode p) :=
  UpperScalarCutProjection.projectedPair rows p native right projection
    (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) right sample.2.1)
    (fun direction => RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain (cutSlots p right))
      ((WholeArrayBucketsLaw.split rows repeats p chosen q right sample.2.1).1 direction))
    sample.1 sample.2.2

theorem pairRecord_observe (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (sample : Sample rows repeats p chosen q right) :
    HierarchicalUsefulCollision.pairRecord native (upperNode p)
        (background rows repeats p chosen q native right projection)
        (observe rows repeats p chosen q native right projection sample) =
      actualPair rows repeats p chosen q native right projection sample := by
  apply Prod.ext
  · exact background_readout rows repeats p chosen q native right projection sample.2.1
  · apply Prod.ext
    · exact (matrix_readout rows repeats p chosen q native right projection sample.2.1).symm
    · exact (replacement_matrix rows p native right projection
        (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) right sample.2.1)
        (fun direction => RecursiveSampler.evaluate F2 repeats (.step chosen q)
          (LeafDomain (cutSlots p right))
          ((WholeArrayBucketsLaw.split rows repeats p chosen q right sample.2.1).1 direction))
        sample.1 sample.2.2).symm

theorem actualPair_law (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (hrows : 0 < rows (j + 1)) :
    (actualLaw rows repeats p chosen q right hrows).pushforward
        (actualPair rows repeats p chosen q native right projection) =
      HierarchicalUsefulCollision.pairLaw native (upperNode p)
        (externalLaw rows repeats p chosen q right)
        (background rows repeats p chosen q native right projection)
        (scalarLaw rows repeats p chosen q native right projection)
        (by simpa only [upperNode_height] using hrows) := by
  rw [HierarchicalUsefulCollision.pairLaw,
    ← observe_law rows repeats p chosen q native right projection hrows,
    FiniteDistribution.pushforward_comp]
  apply congrArg (FiniteDistribution.pushforward _)
  funext sample
  exact (pairRecord_observe rows repeats p chosen q native right projection sample).symm

theorem stoppedProjectedPair_eq (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j (i + 1)) (hproper : i + 1 < j + 1)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (sample : Sample rows repeats p chosen q right) :
    UpperScalarCutProjection.stoppedProjectedPair rows repeats p (.step chosen q) hproper
        native right projection sample =
      actualPair rows repeats p chosen q native right projection sample := rfl

theorem stoppedProjectedPair_law (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j (i + 1)) (hproper : i + 1 < j + 1)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (hrows : 0 < rows (j + 1)) :
    (actualLaw rows repeats p chosen q right hrows).pushforward
        (UpperScalarCutProjection.stoppedProjectedPair rows repeats p (.step chosen q) hproper
          native right projection) =
      HierarchicalUsefulCollision.pairLaw native (upperNode p)
        (externalLaw rows repeats p chosen q right)
        (background rows repeats p chosen q native right projection)
        (scalarLaw rows repeats p chosen q native right projection)
        (by simpa only [upperNode_height] using hrows) :=
  actualPair_law rows repeats p chosen q native right projection hrows

end
end PerfectCompleteness.StoppedUsefulPairLaw

end

end OAI
