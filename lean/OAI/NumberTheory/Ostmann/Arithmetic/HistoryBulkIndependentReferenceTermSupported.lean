import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTermBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTermForwardBActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTermForwardR
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransport

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryPairSmoothXi HistoryBulkReferenceTests
open HistoryBulkReferenceScalarCoordinates HistorySignedSpectatorCRT HistoryGiantReferenceMean
open HistoryBulkResidueNormSum HistoryBulkSpectatorReferenceRaw HistoryFrequencyResidues
open HistoryRepresentativeSourceSeparation HistoryBulkReferenceForwardB HistoryBulkReferenceForwardR

theorem sourceIntegrand_eq_referenceTerm_of_supported
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (V : ℕ→ℕ) (outside : List ℕ) (l K : ℕ)
    (x₀ y₀ x y : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) (s t : ℤ)
    (gp gm : ℕ) (c e : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) V l)
    (hs : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e)).Supported V outside)
    (b sw : ℕ) (X tb td G : ℝ)
    (Jmul : ℤ→ℤ→ℂ) (P Q : ℤ)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator) (hle : l≤K)
    (π : Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length))
    (hold : ∀i, (y₀ i).val=(x₀ (π i)).val)
    (hmatch : ∀i, (y i).val=(x (π i)).val)
    (hfixed : ∀i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length,((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hfixedy : ∀i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length,((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role≠.bulk → (y i).val=(y₀ i).val)
    (hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass y≠0)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l c≠0) (he : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l e≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (V j))
    (hp : 0≤P) (hq : 0≤Q) (had : PairAdmissible (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s gp gm x₀ c) (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t gp gm y₀ e) outside)
    (hn : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c).Supported V outside) (kn : (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e).Supported V outside) :
    sourceIntegrand d C.sources (Template.initial (2*(bulkSize k L/2)) k) V outside l
      (sourceState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) x s) (sourceState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) y t)
      c e Jmul b sw X tb td G P Q =
    referenceTerm C V outside l K x₀ y₀ x y s t gp gm c e hs ks b sw X tb td G Jmul P Q := by
  have hroot : (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) s P.toNat Q.toNat x).Coprime outside ∧
      (assignedRoot C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) t P.toNat Q.toNat y).Coprime outside := by
    simpa only [assignedHistory,decodeHistory_root] using
      And.intro (History.supported_root_coprime hn) (History.supported_root_coprime kn)
  have hB := actual_orderedSourceIndicatorB_eq_one_of_supported C hsep V l s t gp gm P.toNat Q.toNat
    x₀ y₀ x y π hold hmatch c e hs ks hn kn hfixed hx hy hc he hfreq
  have hR := independentReferenceIndicator_eq_one_of_supported K C.sources (2*(bulkSize k L/2)) k l V outside
    x₀ y₀ x y s t gp gm P.toNat Q.toNat c e hfixed hn kn hx hy hfixedy hc he hfreq hle
  simp only [Int.toNat_of_nonneg hp,Int.toNat_of_nonneg hq] at hB
  have hpc (N : ℕ) : (P.toNat:ZMod N)=(P:ZMod N) := by
    rw [←Int.cast_natCast,Int.toNat_of_nonneg hp]
  have hqc (N : ℕ) : (Q.toNat:ZMod N)=(Q:ZMod N) := by
    rw [←Int.cast_natCast,Int.toNat_of_nonneg hq]
  simp only [hpc,hqc] at hR
  unfold referenceTerm
  rw [ite_eq_left hroot,hB,hR,mul_one,mul_one]
  exact HistoryBulkIndependentReferenceTransport.integer_sourceIntegrand_residue_transport
    C.sources (2*(bulkSize k L/2)) k V outside l s t gp gm P Q x₀ y₀ x y π hold hmatch c e
    d hp hq had hs ks hn kn hfixed Jmul b sw X tb td G

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm

end

end OAI
