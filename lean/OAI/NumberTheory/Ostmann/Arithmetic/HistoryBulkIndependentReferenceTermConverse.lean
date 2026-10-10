import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTermBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTermSupport

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryPairBulkTransport HistoryBulkSupportConverse HistoryPairSmoothXi
open HistoryBulkReferenceTests HistoryBulkReferenceScalarCoordinates HistorySignedSpectatorCRT
open HistoryBulkResidueNormSum HistoryBulkSpectatorReferenceRaw HistoryFrequencyResidues
open HistoryBulkIndependentReferenceTerm HistorySignedSpectatorDiagram

theorem supported_of_referenceTerm_ne_zero
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
    (hnew : ∀i, (y i).val=(x (π i)).val)
    (hfixed : ∀i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length,((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hfixedy : ∀i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length,((Template.current (Template.initial (2*(bulkSize k L/2)) k) l).get i).role≠.bulk → (y i).val=(y₀ i).val)
    (hy : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass y≠0)
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x≠0)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l c≠0) (he : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l e≠0)
    (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (V j))
    (hp : 0<P) (hq : 0<Q)
    (hprime : ∀q∈outside,q.Prime) (houtfreq : ∀q∈outside,∀j≤l,V j<q)
    (hz : referenceTerm C V outside l K x₀ y₀ x y s t gp gm c e hs ks b sw X tb td G Jmul P Q≠0) :
    (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l s P.toNat Q.toNat x c).Supported V outside ∧ (assignedHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) V l t P.toNat Q.toNat y e).Supported V outside := by
  unfold referenceTerm at hz
  split_ifs at hz with hroot
  · simp only [mul_ne_zero_iff] at hz
    obtain ⟨⟨⟨⟨_,hB⟩,hR⟩,hD⟩,hXi⟩ := hz
    have hpI : (P.toNat:ℤ)=P := Int.toNat_of_nonneg hp.le
    have hqI : (Q.toNat:ℤ)=Q := Int.toNat_of_nonneg hq.le
    have hpR : (P.toNat:ℝ)=(P:ℝ) := by exact_mod_cast hpI
    have hqR : (Q.toNat:ℝ)=(Q:ℝ) := by exact_mod_cast hqI
    have hpc (N : ℕ) : (P.toNat:ZMod N)=(P:ZMod N) := by
      simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ZMod N)) hpI
    have hqc (N : ℕ) : (Q.toNat:ZMod N)=(Q:ZMod N) := by
      simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ZMod N)) hqI
    apply inserted_pair_supported_of_actual_source_tests C V outside l K x₀ y₀ x y s t gp gm
      P.toNat Q.toNat c e hs ks b sw X tb td G hsep hle π hold hnew hfixed hfixedy hy hx hc he hfreq
      (by omega) (by omega) hroot.1 hroot.2
      ?_ ?_ ?_ (residueTransform d) hprime (fun q _ => actual_residueTransform_zero d q) houtfreq ?_
    · simpa only [hpI,hqI] using hB
    · simpa only [hpR,hqR] using hXi
    · simpa only [hpc,hqc] using hR
    · simpa only [hpc,hqc] using hD
  · exact False.elim (hz rfl)

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTerm

end

end OAI
