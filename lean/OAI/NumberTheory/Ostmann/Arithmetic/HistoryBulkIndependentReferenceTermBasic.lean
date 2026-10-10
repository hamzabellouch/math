import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsActualSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramActual

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryBulkSupportConverse HistoryPairSmoothXi
open HistoryBulkReferenceTests HistoryBulkReferenceScalarCoordinates HistorySignedSpectatorCRT
open HistoryBulkResidueNormSum HistoryBulkSpectatorReferenceRaw HistoryFrequencyResidues
open HistoryGiantReferenceMean HistorySignedXiTransport

def referenceTerm
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (V : ℕ→ℕ) (outside : List ℕ) (l K : ℕ)
    (x₀ y₀ x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (s t : ℤ)
    (gp gm : ℕ) (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) V l)
    (hs : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e)).Supported V outside)
    (b sw : ℕ) (X tb td G : ℝ)
    (Jmul : ℤ→ℤ→ℂ) (P Q : ℤ) : ℂ :=
  if (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) s P.toNat Q.toNat x).Coprime outside ∧
      (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) t P.toNat Q.toNat y).Coprime outside then
    Jmul P Q * (((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c).compensationProduct:ℂ)*((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e).compensationProduct:ℂ)) *
      orderedSourceIndicatorB C.sources (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks
        (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)) x P Q *
      independentReferenceIndicator K (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e) (P,Q) *
      residuePairSpectator (residueTransform d) outside outside.prod (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e) (P,Q) *
      pairedRealXi b sw X tb td G (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks
        (insertOrderedGiants (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs
          (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c))
          (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x)
          (fun a => if a then (Q:ℝ) else (P:ℝ)))
  else 0

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm

end

end OAI
