import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementMatchedFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementMatchedOriginalSamples

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairKernelProductReplacement
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairPattern HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairKernelReplacement HistoryPairReferenceFlagExpectation
open HistoryPairReferenceSourceTransport
variable {d : Decomposition} {Bs BD Bz : ℝ} {depth : ℕ} {L : ℝ} {E : Finset ℕ}
variable {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ}

theorem matchedBlockReference_originalDraw_product_error
    (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator) (mixed : Bool)
    {p : Pattern (pairedHistoryType (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) l)}
    (R : MatchedBlockReference C.sources (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) V outside l p)
    (hroot : RootGiantsAgree R.left.history R.right.history)
    (giants : Bool → PrimeSource)
    (y : OriginalDraw giants C.sources (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) l p)
    (hy : originalDrawMass giants C.sources (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) l p y ≠ 0)
    (hright : RightRootSupported R giants y)
    (hV : ∀j ≤ l, ∀origin, (C.sources origin).AboveFrequency (V j)) :
    let x := originalDrawValues giants C.sources _ l p y ∘
      (typedSourceEquivMatched R.left R.right p R.natDraw R.slot_values R.root_matching).symm
    (∏r : Representative R.left.history R.right.history,
      ((x (representativeMap R.left.history R.right.history r)).toNat : ℝ)) *
      |(∏r, actualProbability mixed R.left.history R.right.history R.left.supported R.right.supported r
          (x (representativeMap R.left.history R.right.history r)).toNat x) -
        ∏r, symbolicKernel mixed R.left.history R.right.history R.left.supported R.right.supported r
          (x (representativeMap R.left.history R.right.history r)).toNat| ≤
      4*2^(Fintype.card (Block p)) * family R.left R.right x := by
  exact matchedBlockReference_product_error C hsep mixed R hroot _
    (matched_originalDrawMass_smallSourceSamples giants R y hy hright) hV

theorem matchedBlockReference_originalDraw_amplitude_error
    (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator) (mixed : Bool)
    {p : Pattern (pairedHistoryType (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) l)}
    (R : MatchedBlockReference C.sources (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) V outside l p)
    (hroot : RootGiantsAgree R.left.history R.right.history)
    (giants : Bool → PrimeSource)
    (y : OriginalDraw giants C.sources (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) l p)
    (hy : originalDrawMass giants C.sources (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) l p y ≠ 0)
    (hright : RightRootSupported R giants y)
    (hV : ∀j ≤ l, ∀origin, (C.sources origin).AboveFrequency (V j)) (A : ℂ) :
    let x := originalDrawValues giants C.sources _ l p y ∘
      (typedSourceEquivMatched R.left R.right p R.natDraw R.slot_values R.root_matching).symm
    (∏r : Representative R.left.history R.right.history,
      ((x (representativeMap R.left.history R.right.history r)).toNat : ℝ)) *
      ‖A * ((∏r, actualProbability mixed R.left.history R.right.history R.left.supported R.right.supported r
          (x (representativeMap R.left.history R.right.history r)).toNat x : ℝ) : ℂ) -
        A * ((∏r, symbolicKernel mixed R.left.history R.right.history R.left.supported R.right.supported r
          (x (representativeMap R.left.history R.right.history r)).toNat : ℝ) : ℂ)‖ ≤
      ‖A‖ * (4*2^(Fintype.card (Block p)) * family R.left R.right x) := by
  dsimp only
  have hh := matchedBlockReference_originalDraw_product_error C hsep mixed R hroot giants y hy hright hV
  dsimp only at hh
  rw [←mul_sub, ←Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ = ‖A‖ * ((∏r : Representative R.left.history R.right.history,
      (((originalDrawValues giants C.sources _ l p y ∘
        (typedSourceEquivMatched R.left R.right p R.natDraw R.slot_values R.root_matching).symm)
        (representativeMap R.left.history R.right.history r)).toNat : ℝ)) * _) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (norm_nonneg A)

end Ostmann.Arithmetic.HistoryPairKernelProductReplacement

end

end OAI
