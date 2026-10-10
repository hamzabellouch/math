import OAI.Computability.PerfectCompleteness.Decoding.CleanPhysicalDecoderLaw
import OAI.Computability.PerfectCompleteness.Decoding.DecoderFamilyLawLemmas

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalHighEvent

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

section NativeTransport

variable {branch : Nat → Nat} {n t : Nat}
  (slots projected target other : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (hs : slots = target) (hp : projected = other)
  (upper : Nodes branch n) (level : Nat) (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

theorem output_answerEquiv
    (answer : CleanPhysicalDecoderLaw.Answers slots projected upper) :
    HEq
      (HierarchicalLeftDecoder.output target upper level hbranch d
        (CleanPhysicalDecoderLaw.answerEquiv slots projected target other hs hp upper answer).1)
      (HierarchicalLeftDecoder.output slots upper level hbranch d answer.1) := by
  cases hs
  cases hp
  rfl

theorem fullRank_answerEquiv
    (answer : CleanPhysicalDecoderLaw.Answers slots projected upper) :
    HierarchicalDecoderTables.fullRank target upper level d
        (HierarchicalLeftDecoder.output target upper level hbranch d
          (CleanPhysicalDecoderLaw.answerEquiv slots projected target other hs hp upper answer).1) =
      HierarchicalDecoderTables.fullRank slots upper level d
        (HierarchicalLeftDecoder.output slots upper level hbranch d answer.1) := by
  cases hs
  cases hp
  rfl

theorem highMeeting_answerEquiv
    (q : ∀ leaf k, MixedSupport.Projection (slots leaf k) (projected leaf k))
    (q' : ∀ leaf k, MixedSupport.Projection (target leaf k) (other leaf k))
    (hq : ∀ leaf k, HEq (q leaf k) (q' leaf k)) (s : Nat)
    (answer : CleanPhysicalDecoderLaw.Answers slots projected upper) :
    ProjectedFiberSquare.highMeeting target other q' upper level hbranch d s
        (CleanPhysicalDecoderLaw.answerEquiv slots projected target other hs hp upper answer).1
        (CleanPhysicalDecoderLaw.answerEquiv slots projected target other hs hp upper answer).2 =
      ProjectedFiberSquare.highMeeting slots projected q upper level hbranch d s
        answer.1 answer.2 := by
  cases hs
  cases hp
  have hqq : q = q' := funext (fun leaf => funext (fun k => eq_of_heq (hq leaf k)))
  cases hqq
  rfl

end NativeTransport

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)
  (hbranch : ∀ k < n, 0 < branch k)

def highEvent (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanPhysicalDecoderLaw.Answers
      (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x) upper) : Bool :=
  ProjectedFiberSquare.highMeeting
    (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
    (CleanPhysicalDecoderLaw.physicalProjection S x) upper (h + 1) hbranch d s
    answer.1 answer.2

theorem physical_fullRank (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) :
    HierarchicalDecoderTables.fullRank (CleanNativeReplay.leftSlots S x) upper (h + 1) d
        (HierarchicalLeftDecoder.output (CleanNativeReplay.leftSlots S x) upper (h + 1)
          hbranch d (CleanPhysicalDecoderLaw.physicalAnswerEquiv S x answer).1) =
      DecoderRankSplit.nativeRank S hbranch x answer := by
  exact (fullRank_answerEquiv _ _ _ _ (CleanNativeReplay.leftSlots_eq S x)
    (CleanNativeReplay.rightSlots_eq S x) upper (h + 1) hbranch d answer).trans
      (DecoderPairHighOutput.nativeRank_eq_fullRank S hbranch x answer).symm

theorem highEvent_physicalAnswerEquiv (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) :
    highEvent S hbranch s x (CleanPhysicalDecoderLaw.physicalAnswerEquiv S x answer) =
      DecoderRankSplit.highAgrees S hbranch s x answer := by
  exact (highMeeting_answerEquiv _ _ _ _ (CleanNativeReplay.leftSlots_eq S x)
    (CleanNativeReplay.rightSlots_eq S x) upper (h + 1) hbranch d _ _
    (CleanPhysicalDecoderLaw.projection_heq S x) s answer).trans
      (DecoderPairHighOutput.highAgrees_eq_highMeeting S hbranch s x answer).symm

variable {Sample : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch rows n t Sample) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule (ZMod 2) (Block rows upper))
  (a : Block rows (CleanPhysicalDecoderLaw.lower S)) (threshold : ℝ)
  (cube : Nat) (hcube : 0 < cube)

theorem probability_pairKernel (s : Nat) (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    (CleanPhysicalDecoderLaw.pairKernel S F κ σ r ρ A W a threshold x).probability
        (highEvent S hbranch s x) =
      (CleanDecoderPairLaw.pairKernel S σ (CleanPhysicalDecoderLaw.useful S F κ)
        r ρ A W a threshold x).probability (DecoderRankSplit.highAgrees S hbranch s x) := by
  rw [CleanPhysicalDecoderLaw.probability_pairKernel S F κ σ r ρ A W a threshold
    cube hcube x hx]
  congr 1
  funext answer
  exact highEvent_physicalAnswerEquiv S hbranch s x answer

theorem mean_probability_eq (s : Nat) :
    (CleanDecoderRate.rawLaw S cube hcube).expectation (fun x =>
      (CleanPhysicalDecoderLaw.pairKernel S F κ σ r ρ A W a threshold x).probability
        (highEvent S hbranch s x)) =
      (CleanDecoderPairLaw.pairLaw S σ (CleanPhysicalDecoderLaw.useful S F κ)
        r ρ A W a threshold cube hcube).probability
        (fun z => DecoderRankSplit.highAgrees S hbranch s z.1 z.2) := by
  rw [CleanDecoderPairLaw.pairLaw, CompletionSoundness.sigmaLaw_probability]
  unfold FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : (CleanDecoderRate.rawLaw S cube hcube).weight x = 0
  · simp only [hx, zero_mul]
  · exact congrArg (fun prob : ℝ => (CleanDecoderRate.rawLaw S cube hcube).weight x * prob)
      (probability_pairKernel S hbranch F κ σ r ρ A W a threshold cube hcube s x hx)

end
end PerfectCompleteness.CleanPhysicalHighEvent

end

end OAI
