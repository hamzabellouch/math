import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementDensityBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyBasic
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkFibreGiantApproximation
open HistoryBulkPrincipalBSquareReplacement
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
  (R : ReferenceFamily C outside l) (X : DensitySources C l)
  (probability corrected mixed : Bool)
  (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
    (Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))

theorem factor_of_some (S : PrincipalSquareReference C outside l p b) (h : R p b=some S) :
    densityPatternFactor R X probability corrected mixed mask p b =
      (if mixed then Frame.extractedDensity (C:=C) (X p b) else 1) *
        ((if mask p b then 1 else 0) *
          (S.principal.value corrected mixed S.newBulk *
            (if probability then probabilityProduct S mixed else bMean S mixed))) := by
  unfold densityPatternFactor densityFactor principalPatternFactor principalValue optionalPrincipalBFactor
  rw [h]

theorem factor_of_none (h : R p b=none) :
    densityPatternFactor R X probability corrected mixed mask p b=0 := by
  unfold densityPatternFactor principalPatternFactor principalValue optionalPrincipalBFactor
  rw [h]
  simp only [mul_zero]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyBasic

end

end OAI
