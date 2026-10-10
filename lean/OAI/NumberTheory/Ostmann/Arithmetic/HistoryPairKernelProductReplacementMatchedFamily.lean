import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationMatchedReference

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

theorem matchedBlockReference_product_error (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator) (mixed : Bool)
    {p : Pattern (pairedHistoryType (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) l)}
    (R : MatchedBlockReference C.sources (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) V outside l p)
    (hroot : RootGiantsAgree R.left.history R.right.history)
    (x : PairKey R.left.history R.right.history → ℤ)
    (hx : SmallSourceSamples C.sources R.left.history R.right.history x)
    (hV : ∀j ≤ l, ∀origin, (C.sources origin).AboveFrequency (V j)) :
    (∏r : Representative R.left.history R.right.history,
      ((x (representativeMap R.left.history R.right.history r)).toNat : ℝ)) *
      |(∏r, actualProbability mixed R.left.history R.right.history R.left.supported R.right.supported r
          (x (representativeMap R.left.history R.right.history r)).toNat x) -
        ∏r, symbolicKernel mixed R.left.history R.right.history R.left.supported R.right.supported r
          (x (representativeMap R.left.history R.right.history r)).toNat| ≤
      4*2^(Fintype.card (Block p)) * family R.left R.right x := by
  have hh := decoded_product_error C hsep mixed R.left R.right hroot x hx hV
  have hcard := Fintype.card_congr (typedBlockEquiv R.left R.right p R.natDraw R.slot_values)
  simpa only [hcard] using hh

end Ostmann.Arithmetic.HistoryPairKernelProductReplacement

end

end OAI
