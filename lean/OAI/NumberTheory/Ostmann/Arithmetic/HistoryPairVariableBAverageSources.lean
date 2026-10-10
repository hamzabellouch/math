import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBAverageError
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBAverageNonzero

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairVariableBAverage
open Construction CanonicalOccurrenceTransport HistorySymbolicEncoding
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairKernelReplacement HistoryCRTIntegration HistorySignedResidueFactorization ResidueHaar
open HistoryBulkReferenceTests HistoryPairVariableBAverageNonzero
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
variable {d : Decomposition} {Bs BD Bz : ℝ} {depth : ℕ} {L : ℝ} {E : Finset ℕ}

private theorem rows_nonzero_of_source_samples
    (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k → ℤ) (hv : SmallSourceSamples C.sources h k v)
    (hrep : ∀ r : Representative h k, v (representativeMap h k r) = (prime h k r : ℤ))
    (hV : ∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j)) :
    ∀ r : Representative h k, ∀ i : Fiber h k r,
      (actualLeftAt h k hs ks v r i : ZMod (prime h k r)) ≠ 0 ∨
        (actualRightAt h k hs ks v r i : ZMod (prime h k r)) ≠ 0 := by
  intro r
  simpa only [actualLeftAt, actualRightAt] using
    variable_rows_nonzero_of_source_samples C hsep h k hh kh hs ks v hv r
      (prime h k r) (representative_prime h k hs ks r) (hrep r) hV

theorem unit_B_averageAt_probability_error_of_source_samples
    (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k → ℤ) (hv : SmallSourceSamples C.sources h k v)
    (hrep : ∀ r : Representative h k, v (representativeMap h k r) = (prime h k r : ℤ))
    (hV : ∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j))
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside) :
    letI : NeZero (representativeModulus h k) := ⟨(representativeModulus_pos h k hs ks).ne'⟩
    ‖average (fun z : UnitPair (representativeModulus h k) =>
        primeResidueIndicatorAt h k hs ks v (z.1,z.2)) -
      ((∏ r : Representative h k,
        actualProbability false h k hs ks r (prime h k r) v) : ℝ)‖ ≤
      (∑ i : Occurrences h k, (1 : ℝ)/(slot h k i).value) *
        (∏ r : Representative h k,
          actualProbability false h k hs ks r (prime h k r) v) := by
  let : NeZero (representativeModulus h k) := ⟨(representativeModulus_pos h k hs ks).ne'⟩
  exact unit_B_averageAt_probability_error h k hs ks v had
    (rows_nonzero_of_source_samples C hsep h k hh kh hs ks v hv hrep hV)

theorem mixed_B_averageAt_probability_error_of_source_samples
    (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k → ℤ) (hv : SmallSourceSamples C.sources h k v)
    (hrep : ∀ r : Representative h k, v (representativeMap h k r) = (prime h k r : ℤ))
    (hV : ∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j))
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible h k outside) :
    letI : NeZero (representativeModulus h k) := ⟨(representativeModulus_pos h k hs ks).ne'⟩
    ‖average (fun z : MixedPair (representativeModulus h k) =>
        primeResidueIndicatorAt h k hs ks v (z.1,z.2)) -
      ((∏ r : Representative h k,
        actualProbability true h k hs ks r (prime h k r) v) : ℝ)‖ ≤
      (∑ i : Occurrences h k, (1 : ℝ)/(slot h k i).value) *
        (∏ r : Representative h k,
          actualProbability true h k hs ks r (prime h k r) v) := by
  let : NeZero (representativeModulus h k) := ⟨(representativeModulus_pos h k hs ks).ne'⟩
  exact mixed_B_averageAt_probability_error h k hs ks v had
    (rows_nonzero_of_source_samples C hsep h k hh kh hs ks v hv hrep hV)

end Ostmann.Arithmetic.HistoryPairVariableBAverage

end

end OAI
