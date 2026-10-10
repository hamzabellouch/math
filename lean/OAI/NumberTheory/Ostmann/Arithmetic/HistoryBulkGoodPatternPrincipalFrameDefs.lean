import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedGoodOperatorReference

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGoodPatternPrincipalFrame
open Construction Conclusion HistoryPairBulkTransport HistoryPairPattern
open HistoryBulkFibreGiantApproximation HistoryBulkGiantCorrectedBounds
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryBulkReferenceScalarCoordinates
open HistoryBulkSelectedIntegralReplacement HistoryBulkReplacementGeometry
open HistoryBulkResidueNormSum HistoryPrincipalIntegralAverage ResidueHaar
open HistoryCRTIntegration HistoryBulkCorrectedXiBounds HistorySelectedJointIntegralBounds
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

def orderedBulkEquiv (r : Frame (l:=l) C outside) :
    (Fin (2^l)×Fin (2*(bulkSize k L/2))) ≃ bulkCoordinates r.left r.right :=
  orderedEquiv (2*(bulkSize k L/2)) k r.left r.right r.left_supported
    (root_matches (assignedLabels C.sources _ _ l r.s r.P.toNat r.Q.toNat
      r.leftSource r.leftChoices))

def principalIntegral (r : Frame (l:=l) C outside) (corrected mixed : Bool) : ℂ :=
  if mixed then
    nestedMixedIntegral L C.giantCenter E
      (if corrected then
        jointCorrectedScalar C (bulkSize k L/2) r.left r.right r.left_supported
          r.right_supported (optionEquiv r.left r.right) (orderedBulkEquiv r)
      else
        jointScalar C (bulkSize k L/2) r.left r.right r.left_supported
          r.right_supported (optionEquiv r.left r.right) (orderedBulkEquiv r))
  else
    nestedPrimeIntegral L C.giantCenter E
      (if corrected then
        jointCorrectedScalar C (bulkSize k L/2) r.left r.right r.left_supported
          r.right_supported (boolEquiv r.left r.right) (orderedBulkEquiv r)
      else
        jointScalar C (bulkSize k L/2) r.left r.right r.left_supported
          r.right_supported (boolEquiv r.left r.right) (orderedBulkEquiv r))

def principalOperator (r : Frame (l:=l) C outside) (corrected mixed : Bool)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ := by
  have : NeZero (bulkModulus r.left r.right outside k) :=
    ⟨actual_bulk_modulus_ne_zero r.left r.right r.left_supported r.right_supported
      r.outside_primes k⟩
  exact principalIntegral r corrected mixed *
    average (rootTest true mixed d r.left r.right r.left_supported r.right_supported
      r.outside_primes hV σ k)

end Ostmann.Arithmetic.HistoryBulkGoodPatternPrincipalFrame

end

end OAI
