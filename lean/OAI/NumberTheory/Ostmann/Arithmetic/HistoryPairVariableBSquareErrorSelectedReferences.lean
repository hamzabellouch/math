import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBAverageSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedKernel
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportDecodedData

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected
open Construction CanonicalOccurrenceTransport HistorySymbolicEncoding
open HistoryPairPattern HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairKernelReplacement HistoryCompensationBiasedKernelSum
open HistoryPairVariableBSquareErrorSelectedKernel CompensationEqualityPatterns Conclusion
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure DecodedSquareReference (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (p : Pattern τ)
    (b : Block p → CommonSample C.sources origin) (V : ℕ → ℕ)
    (outside : List ℕ) (l : ℕ) where
  leftDraw : DecodedDraw C.sources (Template.initial (2*(bulkSize k L/2)) k) V outside l
  rightDraw : DecodedDraw C.sources (Template.initial (2*(bulkSize k L/2)) k) V outside l
  leftMass : choicesMass C.sources _ V l leftDraw.choices ≠ 0
  rightMass : choicesMass C.sources _ V l rightDraw.choices ≠ 0
  sample : PairKey leftDraw.history rightDraw.history → ℤ
  sourceSamples : SmallSourceSamples C.sources leftDraw.history rightDraw.history sample
  representative : Block p ≃ Representative leftDraw.history rightDraw.history
  prime_eq : ∀q, prime leftDraw.history rightDraw.history (representative q) = (b q).val
  sample_representative : ∀r, sample (representativeMap leftDraw.history rightDraw.history r) =
    (prime leftDraw.history rightDraw.history r : ℤ)
  admissible : HistoryRepresentativeSourceSeparation.PairAdmissible leftDraw.history rightDraw.history outside

namespace DecodedSquareReference
variable {C : InitialSourceChoice d Bs BD Bz k L E} {origin τ : ι → ℕ}
    {p : Pattern τ} {b : Block p → CommonSample C.sources origin}
    {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ}

def toSourceReference (r : DecodedSquareReference C origin τ p b V outside l) :
    SourcePatternReference C origin τ p b V outside l where
  left := r.leftDraw.history
  right := r.rightDraw.history
  hs := r.leftDraw.supported
  ks := r.rightDraw.supported
  representative := r.representative
  sourceLeft := r.leftDraw.labels
  sourceRight := r.rightDraw.labels
  sample := r.sample
  sourceSamples := r.sourceSamples
  sampled_representative := by intro q; rw [r.sample_representative,r.prime_eq]

omit [DecidableEq ι] in

theorem probability_product_eq (r : DecodedSquareReference C origin τ p b V outside l)
    (mixed : Bool) :
    (∏q : Block p, actualProbability mixed r.leftDraw.history r.rightDraw.history
      r.leftDraw.supported r.rightDraw.supported (r.representative q) (b q).val r.sample) =
    ∏q : Representative r.leftDraw.history r.rightDraw.history,
      actualProbability mixed r.leftDraw.history r.rightDraw.history
        r.leftDraw.supported r.rightDraw.supported q
        (prime r.leftDraw.history r.rightDraw.history q) r.sample := by
  simp_rw [←r.prime_eq]
  exact r.representative.prod_comp (fun q => actualProbability mixed r.leftDraw.history r.rightDraw.history
    r.leftDraw.supported r.rightDraw.supported q
    (prime r.leftDraw.history r.rightDraw.history q) r.sample)

end DecodedSquareReference
end Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected

end

end OAI
