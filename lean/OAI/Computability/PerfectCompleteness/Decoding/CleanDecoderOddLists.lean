import OAI.Computability.PerfectCompleteness.Construction.NativeLeafAlphabet
import OAI.Computability.PerfectCompleteness.Construction.SourceLocalOddLists
import OAI.Computability.PerfectCompleteness.Decoding.CleanEndpointProjection
import OAI.Computability.PerfectCompleteness.Decoding.CleanLeftDecoderLemmas
import OAI.Computability.PerfectCompleteness.Foundations.OddListAlphabetTransport

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderOddLists

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open ChildBlockProjection CleanDecoderContext
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

variable {branch rows repeats : Nat → Nat} {n h t v m s : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (E : Exposed branch rows repeats n h t v m upper d)

def nativeLeaf (_E : Exposed branch rows repeats n h t v m upper d)
    (leaf : Slots branch (h + 1)) : Slots branch (Nodes.height (lower _E)) :=
  cast (congrArg (Slots branch) (lowerHeight upper d).symm) leaf

private theorem slotEmbedding_cast_target {a b c : Nat} (hab : b = c)
    (p : Path branch a b) (leaf : Slots branch c) :
    (hab ▸ p).slotEmbedding leaf =
      p.slotEmbedding (cast (congrArg (Slots branch) hab.symm) leaf) := by
  cases hab
  rfl

theorem nativeLeaf_embedding (leaf : Slots branch (h + 1)) :
    (Nodes.path (lower E)).slotEmbedding (nativeLeaf E leaf) =
      (path E).slotEmbedding leaf := by
  rw [← E.cut.slots_agree]
  unfold path CleanRightDecoder.fullPath CleanRightDecoder.suffix
  simp only [Path.slotEmbedding_append, slotEmbedding_cast_target, nativeLeaf]

theorem nativeLeaf_slots (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (leaf : Slots branch (h + 1)) :
    nodeSlots (CutSlotAssembly.fill (path E) E.outside inside) (lower E)
      (nativeLeaf E leaf) = inside leaf := by
  change CutSlotAssembly.fill (path E) E.outside inside
    ((Nodes.path (lower E)).slotEmbedding (nativeLeaf E leaf)) = inside leaf
  rw [nativeLeaf_embedding]
  exact CutSlotAssembly.fill_at_cut (path E) E.outside inside leaf

abbrev leftNative (own : LeftOwn E) := nodeSlots (leftSlots E own) (lower E)
abbrev rightNative (own : RightOwn E) := nodeSlots (rightSlots E own) (lower E)

def designatedLeaf (i : CleanChildren E) := nativeLeaf E (i.val, E.designated i.val)

theorem leftNative_designated (own : LeftOwn E) (i : CleanChildren E) :
    leftNative E own (designatedLeaf E i) = SourceAnswerEquiv.leftSlots E.clauses (own i) := by
  exact (nativeLeaf_slots E
    (CleanEndpointSlots.leftInside E.clauses E.designated E.clean E.visible own)
    (i.val, E.designated i.val)).trans
      (CleanEndpointProjection.leftInside_designated
        E.clauses E.designated E.clean E.visible own i)

theorem rightNative_designated (own : RightOwn E) (i : CleanChildren E) :
    rightNative E own (designatedLeaf E i) = SourceAnswerEquiv.rightSlots E.clauses (own i) := by
  exact (nativeLeaf_slots E
    (CleanEndpointSlots.rightInside E.clauses E.designated E.clean E.visible E.projected own)
    (i.val, E.designated i.val)).trans
      (CleanEndpointProjection.rightInside_designated
        E.clauses E.designated E.clean E.visible E.projected own i)

def leftEncoding (own : LeftOwn E) (i : CleanChildren E) :
    LeafDomain (leftNative E own) (designatedLeaf E i) ≃ SourceOddLists.LeftLabels t :=
  NativeLeafAlphabet.nativeLeftEquiv E.clauses (own i) (leftNative_designated E own i)

def rightEncoding (own : RightOwn E) (i : CleanChildren E) :
    LeafDomain (rightNative E own) (designatedLeaf E i) ≃ SourceOddLists.RightLabels t :=
  NativeLeafAlphabet.nativeRightEquiv E.clauses (own i) (rightNative_designated E own i)

abbrev Occurrences := CleanChildren E → SourceOddLists.Occurrences m t

def leftQuestions (e : Occurrences E) : LeftOwn E := fun i => SourceOddLists.left (e i)
def rightQuestions (e : Occurrences E) : RightOwn E :=
  fun i => SourceOddLists.right E.clauses (e i)

def fullProjection (e : Occurrences E) : ∀ leaf k,
    MixedSupport.Projection (leftSlots E (leftQuestions E e) leaf k)
      (rightSlots E (rightQuestions E e) leaf k) :=
  CutProjectionAssembly.fillProjection (path E) E.outside
    (CleanEndpointSlots.leftInside E.clauses E.designated E.clean E.visible (leftQuestions E e))
    (CleanEndpointSlots.rightInside E.clauses E.designated E.clean E.visible E.projected
      (rightQuestions E e))
    (CleanEndpointProjection.insideProjection E.clauses E.designated E.clean E.visible
      E.projected E.cleanProjected e)

theorem nativeProjection_designated (e : Occurrences E) (i : CleanChildren E) (k : Fin t) :
    HEq (nodeProjection (fullProjection E e) (lower E) (designatedLeaf E i) k)
      (SourceAnswerEquiv.slotProjection E.clauses (e i) k) := by
  have hcut := (CutProjectionAssembly.fillProjection_at_cut (path E) E.outside
    (CleanEndpointSlots.leftInside E.clauses E.designated E.clean E.visible (leftQuestions E e))
    (CleanEndpointSlots.rightInside E.clauses E.designated E.clean E.visible E.projected
      (rightQuestions E e))
    (CleanEndpointProjection.insideProjection E.clauses E.designated E.clean E.visible
      E.projected E.cleanProjected e)
    (i.val, E.designated i.val) k).trans
      (CleanEndpointProjection.insideProjection_designated E.clauses E.designated E.clean
        E.visible E.projected E.cleanProjected e i k)
  exact Eq.mpr (congrArg (fun leaf : Slots branch n =>
    HEq (fullProjection E e leaf k) (SourceAnswerEquiv.slotProjection E.clauses (e i) k))
    (nativeLeaf_embedding E (i.val, E.designated i.val))) hcut

theorem projection_encode (e : Occurrences E) (i : CleanChildren E)
    (x : LeafDomain (leftNative E (leftQuestions E e)) (designatedLeaf E i)) :
    rightEncoding E (rightQuestions E e) i
        (MixedSupport.projectionMap
          (nodeProjection (fullProjection E e) (lower E) (designatedLeaf E i)) x) =
      SourceOddLists.projection E.clauses (e i)
        (leftEncoding E (leftQuestions E e) i x) :=
  NativeLeafAlphabet.projection_encode E.clauses (e i)
    (leftNative_designated E (leftQuestions E e) i)
    (rightNative_designated E (rightQuestions E e) i) _
    (nativeProjection_designated E e i) x

variable (hbranch : ∀ k < n, 0 < branch k)

def target (seed : LeftSeed E) (e : Occurrences E) :=
  DecoderSourcePullback.upperTarget (fullProjection E e) upper (seed (leftQuestions E e))

def leftResponse (positive : 0 < s) (seed : LeftSeed E) (own : LeftOwn E)
    (i : CleanChildren E) : OddLists.OddList s (SourceOddLists.LeftLabels t) :=
  OddLists.OddList.map (leftEncoding E own i)
    (SourceLocalOddLists.extract positive (leftNative E own) (leftForm E hbranch seed own)
      (designatedLeaf E i) ((leftEncoding E own i).symm (fun _ => 0)))

def rightResponse (positive : 0 < s) (seed : RightSeed E) (own : RightOwn E)
    (i : CleanChildren E) : OddLists.OddList s (SourceOddLists.RightLabels t) :=
  OddLists.OddList.map (rightEncoding E own i)
    (SourceLocalOddLists.extract positive (rightNative E own) (rightForm E hbranch seed own)
      (designatedLeaf E i) ((rightEncoding E own i).symm (fun _ => false)))

def strategy (positive : 0 < s) (leftSeed : LeftSeed E) (rightSeed : RightSeed E) :
    Strategy (LeftOwn E) (RightOwn E)
      (CleanChildren E → OddLists.OddList s (SourceOddLists.LeftLabels t))
      (CleanChildren E → OddLists.OddList s (SourceOddLists.RightLabels t)) :=
  (leftResponse E hbranch positive leftSeed, rightResponse E hbranch positive rightSeed)

theorem forms_agree (leftSeed : LeftSeed E) (rightSeed : RightSeed E)
    (e : Occurrences E) (htarget : rightSeed (rightQuestions E e) = target E leftSeed e)
    (f g : H (rightNative E (rightQuestions E e))) :
    rightForm E hbranch rightSeed (rightQuestions E e) f g =
      OddListExtraction.multiplicationForm (H (leftNative E (leftQuestions E e)))
        (leftOutput E hbranch leftSeed (leftQuestions E e))
        (HPullback (nodeProjection (fullProjection E e) (lower E)) f)
        (HPullback (nodeProjection (fullProjection E e) (lower E)) g) := by
  change RightDecoderDescendant.form (rightSlots E (rightQuestions E e)) upper (lower E)
    E.cut (DecoderSourcePullback.upperBranch upper hbranch)
      (rightSeed (rightQuestions E e)) f g = _
  rw [htarget]
  exact DecoderSourcePullback.form_upperTarget (fullProjection E e) upper (h + 1)
    hbranch d E.cut (leftSeed (leftQuestions E e)) f g

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : CleanLeftDecoder.Useful (leftExposed E) upper (h + 1))

theorem responses_accept (positive : 0 < s) (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (leftSeed : LeftSeed E)
    (hsupport : (CleanLeftDecoder.seedLaw (leftExposed E) upper (h + 1)
      σ useful r ρ A).weight leftSeed ≠ 0)
    (rightSeed : RightSeed E) (e : Occurrences E)
    (htarget : rightSeed (rightQuestions E e) = target E leftSeed e)
    (hrank : OddListExtraction.formRank (H (leftNative E (leftQuestions E e)))
      (leftForm E hbranch leftSeed (leftQuestions E e)) ≤ s)
    (i : CleanChildren E) :
    OddLists.OddList.map (SourceOddLists.projection E.clauses (e i))
      (leftResponse E hbranch positive leftSeed (leftQuestions E e) i) =
      rightResponse E hbranch positive rightSeed (rightQuestions E e) i := by
  have hnorm := CleanLeftDecoder.supported_output_normalized (leftExposed E) upper (h + 1)
    σ useful hbranch r ρ hρ A leftSeed hsupport d (leftQuestions E e)
  have hnative := SourceLocalOddLists.extract_accepts positive
    (nodeProjection (fullProjection E e) (lower E)) (designatedLeaf E i)
    (leftForm E hbranch leftSeed (leftQuestions E e))
    (rightForm E hbranch rightSeed (rightQuestions E e))
    (leftOutput E hbranch leftSeed (leftQuestions E e)) rfl
    (HierarchicalLeftDecoder.lowerOne (leftSlots E (leftQuestions E e)) upper (h + 1)
      hbranch d).property hnorm hrank (forms_agree E hbranch leftSeed rightSeed e htarget)
    ((leftEncoding E (leftQuestions E e) i).symm (fun _ => 0))
    ((rightEncoding E (rightQuestions E e) i).symm (fun _ => false))
  exact OddLists.OddList.map_commutes _ (leftEncoding E (leftQuestions E e) i)
    (rightEncoding E (rightQuestions E e) i) (SourceOddLists.projection E.clauses (e i))
    (fun x => (projection_encode E e i x).symm) _ _ hnative

theorem strategy_wins (positive : 0 < s) (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (leftSeed : LeftSeed E)
    (hsupport : (CleanLeftDecoder.seedLaw (leftExposed E) upper (h + 1)
      σ useful r ρ A).weight leftSeed ≠ 0)
    (rightSeed : RightSeed E) (e : Occurrences E)
    (htarget : rightSeed (rightQuestions E e) = target E leftSeed e)
    (hrank : OddListExtraction.formRank (H (leftNative E (leftQuestions E e)))
      (leftForm E hbranch leftSeed (leftQuestions E e)) ≤ s) :
    (IndexedRepetition.game (SourceOddLists.game s E.clauses t) (CleanChildren E)).wins
      (strategy E hbranch positive leftSeed rightSeed) e = true := by
  simp only [OccurrenceGame.wins, IndexedRepetition.game, SourceOddLists.game,
    OddListGame.game, OccurrenceGame.ofProjection, strategy, decide_eq_true_eq]
  exact responses_accept E hbranch σ useful positive r ρ hρ A
    leftSeed hsupport rightSeed e htarget hrank

end
end PerfectCompleteness.CleanDecoderOddLists

end

end OAI
