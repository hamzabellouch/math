import OAI.Computability.PerfectCompleteness.Decoding.CleanPhysicalDecoderLaw
import OAI.Computability.PerfectCompleteness.Decoding.ProjectedRawDecoderLaw
import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayRawAssembly

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalProjectedMeeting

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

attribute [local instance] CleanPhysicalDecoderLaw.nativeLeftFintype RightDecoder.scalarFintype

section TapeCast

variable {branch rows repeats : Nat → Nat} {n t : Nat}

private theorem evaluate_uncastTape
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (cut : OwnInputReference.Cut upper lower)
    {k : Nat} (hk : Nodes.height lower = k)
    (tape : WholeArraySampler.Tape rows repeats
      ((Nodes.path upper).append (hk ▸ cut.path)) slots) :
    WholeArraySampler.evaluate rows repeats ((Nodes.path upper).append cut.path) slots
        (CleanPhysicalDecoderLaw.uncastTape slots upper lower cut hk tape) =
      WholeArraySampler.evaluate rows repeats ((Nodes.path upper).append (hk ▸ cut.path)) slots tape := by
  cases hk
  rfl

end TapeCast

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev lower := CleanPhysicalDecoderLaw.lower S

def rawSample (W : Submodule F2 (Block rows upper)) (x : CleanDecoderRate.Sample S) :
    OwnInputReference.RawSample (CleanNativeReplay.rightSlots S x) rows upper (lower S) W repeats S.cut :=
  WholeArrayInteriorOwnInputLaw.exposedRead rows repeats (CleanNativeReplay.rightSlots S x)
    upper (lower S) S.cut W
    (CleanPhysicalDecoderLaw.uncastTape (CleanNativeReplay.rightSlots S x) upper (lower S) S.cut
      (CleanDecoderContext.lowerHeight upper d) (CleanPhysicalDecoderLaw.rightWholeTape S x))

abbrev visible (W : Submodule F2 (Block rows upper)) (x : CleanDecoderRate.Sample S) :=
  (rawSample S W x).2

theorem raw_arrays (W : Submodule F2 (Block rows upper)) (x : CleanDecoderRate.Sample S) :
    OwnInputRawAssembly.arrays (CleanNativeReplay.rightSlots S x) rows upper (lower S) W
      repeats S.cut (rawSample S W x) = CleanPhysicalDecoderLaw.rightArrays S x := by
  have hraw := WholeArrayRawAssembly.arrays_exposedRead rows repeats
    (CleanNativeReplay.rightSlots S x) upper (lower S) S.cut W
    (CleanPhysicalDecoderLaw.uncastTape (CleanNativeReplay.rightSlots S x) upper (lower S) S.cut
      (CleanDecoderContext.lowerHeight upper d) (CleanPhysicalDecoderLaw.rightWholeTape S x))
  exact hraw.trans (evaluate_uncastTape (CleanNativeReplay.rightSlots S x) upper (lower S) S.cut
    (CleanDecoderContext.lowerHeight upper d) (CleanPhysicalDecoderLaw.rightWholeTape S x))

theorem projected_raw_arrays (W : Submodule F2 (Block rows upper))
    (x : CleanDecoderRate.Sample S) :
    ProjectedRawAssembly.arrays (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
      (CleanPhysicalDecoderLaw.physicalProjection S x) rows upper (lower S) W repeats S.cut
      (rawSample S W x) = CleanPhysicalDecoderLaw.leftArrays S x := by
  unfold ProjectedRawAssembly.arrays
  rw [raw_arrays]
  exact (CleanPhysicalCanonicalQuery.arrays_pullback rows repeats (CleanDecoderRate.path S)
    S.outside S.placeholder S.clauses S.designated x S.exterior).symm

theorem rightInput_eq_readInput (W : Submodule F2 (Block rows upper))
    (a : Block rows (lower S)) (x : CleanDecoderRate.Sample S) :
    CleanPhysicalDecoderLaw.rightInput S W a x =
      OwnInputReference.readInput (CleanNativeReplay.rightSlots S x) rows upper (lower S) W a
        (OwnInputRawAssembly.scalarEval (CleanNativeReplay.rightSlots S x) upper (lower S)
          repeats S.cut) (visible S W x) :=
  CleanPhysicalDecoderLaw.rightInput_eq_ownInput S W a x

variable {Sample : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch rows n t Sample) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (a : Block rows (lower S)) (threshold : ℝ)

theorem leftLaw_eq_visible (x : CleanDecoderRate.Sample S) :
    CleanPhysicalDecoderLaw.leftLaw S F κ σ r ρ A x =
      HierarchicalProjectedMeeting.leftLaw
        (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
        (CleanPhysicalDecoderLaw.physicalProjection S x) upper (h + 1)
        (HierarchicalProjectedRawPrediction.visibleBackground
          (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
          (CleanPhysicalDecoderLaw.physicalProjection S x) rows upper (lower S) A repeats S.cut
          (visible S (LinearMap.ker A) x))
        (F.original (CleanNativeReplay.leftSlots S x))
        (F.arrays (CleanNativeReplay.leftSlots S x))
        (F.lowerEvent (CleanNativeReplay.leftSlots S x)) κ σ ρ A
        (HierarchicalProjectedRawPrediction.known (CleanNativeReplay.rightSlots S x)
          rows upper (lower S) A repeats S.cut (visible S (LinearMap.ker A) x)) := by
  change CleanPhysicalDecoderLaw.adviceLaw F (CleanNativeReplay.leftSlots S x) upper (h + 1) κ
    (CleanPhysicalDecoderLaw.leftArrays S x) σ r ρ A = _
  rw [← projected_raw_arrays S (LinearMap.ker A) x]
  exact ProjectedRawDecoderLaw.adviceLaw_eq_leftLaw
    (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
    (CleanPhysicalDecoderLaw.physicalProjection S x) rows upper (lower S) (h + 1)
    (F.original (CleanNativeReplay.leftSlots S x))
    (F.arrays (CleanNativeReplay.leftSlots S x))
    (F.lowerEvent (CleanNativeReplay.leftSlots S x)) κ σ ρ A repeats S.cut
    (rawSample S (LinearMap.ker A) x)

def visiblePairKernel (x : CleanDecoderRate.Sample S) :=
  (HierarchicalProjectedMeeting.leftLaw
    (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
    (CleanPhysicalDecoderLaw.physicalProjection S x) upper (h + 1)
    (HierarchicalProjectedRawPrediction.visibleBackground
      (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
      (CleanPhysicalDecoderLaw.physicalProjection S x) rows upper (lower S) A repeats S.cut
      (visible S (LinearMap.ker A) x))
    (F.original (CleanNativeReplay.leftSlots S x))
    (F.arrays (CleanNativeReplay.leftSlots S x))
    (F.lowerEvent (CleanNativeReplay.leftSlots S x)) κ σ ρ A
    (HierarchicalProjectedRawPrediction.known (CleanNativeReplay.rightSlots S x)
      rows upper (lower S) A repeats S.cut (visible S (LinearMap.ker A) x))).product
    (RightDecoder.law (CleanNativeReplay.rightSlots S x) rows upper (lower S)
      (LinearMap.ker A) a repeats S.cut σ
      (OwnInputReference.readInput (CleanNativeReplay.rightSlots S x) rows upper (lower S)
        (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval (CleanNativeReplay.rightSlots S x) upper (lower S)
          repeats S.cut) (visible S (LinearMap.ker A) x)) threshold)

theorem pairKernel_eq_visible (x : CleanDecoderRate.Sample S) :
    CleanPhysicalDecoderLaw.pairKernel S F κ σ r ρ A (LinearMap.ker A) a threshold x =
      visiblePairKernel S F κ σ r ρ A a threshold x := by
  unfold CleanPhysicalDecoderLaw.pairKernel visiblePairKernel
  rw [leftLaw_eq_visible]
  unfold CleanPhysicalDecoderLaw.rightLaw
  rw [rightInput_eq_readInput]

theorem meeting_probability_eq (cube : Nat) (hcube : 0 < cube)
    (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    (visiblePairKernel S F κ σ r ρ A a threshold x).probability
      (fun answer => decide ((ProjectedNodeEmbedding.intoOriginal
        (CleanPhysicalDecoderLaw.physicalProjection S x) upper).dualMap answer.1 = answer.2)) =
      (CleanDecoderPairLaw.pairKernel S σ (CleanPhysicalDecoderLaw.useful S F κ)
        r ρ A (LinearMap.ker A) a threshold x).probability
        (fun answer => decide (answer.2 = DecoderSourcePullback.upperTarget
          (CleanDecoderOddLists.fullProjection (CleanDecoderPairLaw.context S x)
            (CleanDecoderPairLaw.occurrences S x)) upper answer.1)) := by
  rw [← pairKernel_eq_visible]
  have hevent :
      (fun answer : CleanPhysicalDecoderLaw.Answers
          (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x) upper =>
        decide ((ProjectedNodeEmbedding.intoOriginal
          (CleanPhysicalDecoderLaw.physicalProjection S x) upper).dualMap answer.1 = answer.2)) =
      (fun answer => decide (answer.2 = DecoderSourcePullback.upperTarget
        (CleanPhysicalDecoderLaw.physicalProjection S x) upper answer.1)) := by
    funext answer
    rw [ProjectedNodeEmbedding.dualMap_eq_upperTarget]
    exact decide_eq_decide.mpr eq_comm
  rw [hevent]
  exact CleanPhysicalDecoderLaw.meeting_probability_eq S F κ σ r ρ A (LinearMap.ker A)
    a threshold cube hcube x hx

end
end PerfectCompleteness.CleanPhysicalProjectedMeeting

end

end OAI
