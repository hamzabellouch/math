import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequency
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTermBasic
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

def orderedReferenceTerm
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (V : ℕ→ℕ) (outside : List ℕ) (l K : ℕ)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
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
      independentRTest K (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) σ (P,Q)
        (sourceBulkUnits ((pairedFrequencyProduct (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e))^(K+2)) C.sources (2*(bulkSize k L/2)) k l x) *
      residuePairSpectator (residueTransform d) outside outside.prod (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e) (P,Q) *
      pairedRealXi b sw X tb td G (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs ks
        (insertOrderedGiants (2*(bulkSize k L/2)) k (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) hs
          (root_matches (assignedLabels C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c))
          (orderedSourceValues C.sources (2*(bulkSize k L/2)) k l x)
          (fun a => if a then (Q:ℝ) else (P:ℝ)))
  else 0

theorem referenceTerm_eq_orderedReferenceTerm
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (V : ℕ→ℕ) (outside : List ℕ) (l K : ℕ)
    (x₀ y₀ x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (s t : ℤ)
    (gp gm : ℕ) (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) V l)
    (hs : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e)).Supported V outside)
    (b sw : ℕ) (X tb td G : ℝ)
    (Jmul : ℤ→ℤ→ℂ) (P Q : ℤ)
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length))
    (hπ : ∀i, ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role=.bulk ↔ ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get (π i)).role=.bulk)
    (hnew : ∀i, (y i).val=(x (π i)).val)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (V j)) :
    referenceTerm C V outside l K x₀ y₀ x y s t gp gm c e hs ks b sw X tb td G Jmul P Q =
    orderedReferenceTerm C V outside l K
      (HistoryBulkIndependentReferenceFrequency.inducedBulkPermutation (2*(bulkSize k L/2)) k l π hπ)
      x₀ y₀ x y s t gp gm c e hs ks b sw X tb td G Jmul P Q := by
  have hR := HistoryBulkIndependentReferenceFrequency.independentRTest_source_eq_reference_of_fullPermutation
    K (2*(bulkSize k L/2)) k l C.sources V (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e)
    (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) s P.toNat Q.toNat x)
    (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) t P.toNat Q.toNat y) c e x y π hπ hnew
    rfl rfl hs ks hx hfreq (P,Q)
  unfold referenceTerm orderedReferenceTerm
  rw [hR]
  rfl

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm

end

end OAI
