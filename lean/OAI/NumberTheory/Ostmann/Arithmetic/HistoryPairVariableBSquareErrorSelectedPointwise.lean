import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBAverageSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedReciprocal
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportDecodedData

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected
open Construction CanonicalOccurrenceTransport HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives HistoryPairRepresentativeVariables HistoryPairKernelReplacement
open HistoryCRTIntegration HistorySignedResidueFactorization HistoryBulkReferenceTests ResidueHaar
open HistoryPairVariableBAverage Conclusion Filter
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}

def decodedBProbabilityError (mixed : Bool)
    (D E : DecodedDraw sources seed V outside l)
    (v : PairKey D.history E.history → ℤ) : ℂ :=
  letI : NeZero (representativeModulus D.history E.history) :=
    ⟨(representativeModulus_pos D.history E.history D.supported E.supported).ne'⟩
  (if mixed then
    average (fun z : MixedPair (representativeModulus D.history E.history) =>
      primeResidueIndicatorAt D.history E.history D.supported E.supported v (z.1,z.2))
   else
    average (fun z : UnitPair (representativeModulus D.history E.history) =>
      primeResidueIndicatorAt D.history E.history D.supported E.supported v (z.1,z.2))) -
    ((∏ r : Representative D.history E.history,
      actualProbability mixed D.history E.history D.supported E.supported r
        (prime D.history E.history r) v) : ℝ)

theorem selected_decoded_B_probability_error_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (F : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L F),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10 : ℝ)*L) →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l : ℕ, l ≤ k →
      let seed := Template.initial (2*(bulkSize k L/2)) k
      ∀ (V : ℕ → ℕ) (outside : List ℕ) (D E : DecodedDraw C.sources seed V outside l),
      choicesMass C.sources seed V l D.choices ≠ 0 →
      choicesMass C.sources seed V l E.choices ≠ 0 →
      ∀ {spectator : PrimeSource}, C.CrossRoleSeparation spectator →
      (∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j)) →
      ∀ (v : PairKey D.history E.history → ℤ),
      SmallSourceSamples C.sources D.history E.history v →
      (∀ r : Representative D.history E.history,
        v (representativeMap D.history E.history r) = (prime D.history E.history r : ℤ)) →
      HistoryRepresentativeSourceSeparation.PairAdmissible D.history E.history outside →
      ∀ mixed : Bool,
      ‖decodedBProbabilityError mixed D E v‖ ≤
        (4*k*2^k : ℕ) * Real.exp (-Real.exp ((39/10000 : ℝ)*L)) *
          (∏ r : Representative D.history E.history,
            actualProbability mixed D.history E.history D.supported E.supported r
              (prime D.history E.history r) v) := by
  filter_upwards [selected_decoded_reciprocal_sum_eventually d Bs BD Bz hk] with L hL
  intro F C hG hGu hcl hcu hb hd l hl
  dsimp only
  intro V outside D E hD hE spectator hsep hV v hv hrep had mixed
  have hrec := hL F C hG hGu hcl hcu hb hd l hl V D.root E.root D.choices E.choices
    D.sourceMatch E.sourceMatch hD hE
  have hprob : 0 ≤ ∏ r : Representative D.history E.history,
      actualProbability mixed D.history E.history D.supported E.supported r
        (prime D.history E.history r) v := by
    apply Finset.prod_nonneg
    intro r _
    have hp := representative_prime D.history E.history D.supported E.supported r
    let : Fact (prime D.history E.history r).Prime := ⟨hp⟩
    cases mixed
    · simp only [actualProbability, hp, dite_true, Bool.false_eq_true, ite_false]
      exact (unit_probability_bounds _ _ _).1
    · simp only [actualProbability, hp, dite_true, ite_true]
      exact (mixed_probability_bounds _ _ _).1
  have herror : ‖decodedBProbabilityError mixed D E v‖ ≤
      (∑ i : Occurrences D.history E.history,
        (1 : ℝ)/(slot D.history E.history i).value) *
      (∏ r : Representative D.history E.history,
        actualProbability mixed D.history E.history D.supported E.supported r
          (prime D.history E.history r) v) := by
    cases mixed
    · simpa only [decodedBProbabilityError, Bool.false_eq_true, ite_false] using
        unit_B_averageAt_probability_error_of_source_samples C hsep D.history E.history
          D.labels E.labels D.supported E.supported v hv hrep hV had
    · simpa only [decodedBProbabilityError, ite_true] using
        mixed_B_averageAt_probability_error_of_source_samples C hsep D.history E.history
          D.labels E.labels D.supported E.supported v hv hrep hV had
  exact herror.trans (mul_le_mul_of_nonneg_right hrec hprob)

end Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected

end

end OAI
