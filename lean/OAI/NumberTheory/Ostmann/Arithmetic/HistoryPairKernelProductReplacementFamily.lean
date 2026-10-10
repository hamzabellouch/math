import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSelectedReference

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

theorem decoded_product_error (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator) (mixed : Bool)
    (D F : DecodedDraw C.sources (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) V outside l)
    (hroot : RootGiantsAgree D.history F.history)
    (x : PairKey D.history F.history → ℤ)
    (hx : SmallSourceSamples C.sources D.history F.history x)
    (hV : ∀j ≤ l, ∀origin, (C.sources origin).AboveFrequency (V j)) :
    (∏r : Representative D.history F.history,
      ((x (representativeMap D.history F.history r)).toNat : ℝ)) *
      |(∏r, actualProbability mixed D.history F.history D.supported F.supported r
          (x (representativeMap D.history F.history r)).toNat x) -
        ∏r, symbolicKernel mixed D.history F.history D.supported F.supported r
          (x (representativeMap D.history F.history r)).toNat| ≤
      4*2^(Fintype.card (Representative D.history F.history)) * family D F x :=
  sampled_product_error_of_source_samples C hsep mixed D.history F.history D.labels F.labels
    D.supported F.supported hroot x hx hV

theorem blockReference_product_error (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator) (mixed : Bool)
    {p : Pattern (pairedHistoryType (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) l)}
    (R : BlockReference C.sources (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) V outside l p)
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
