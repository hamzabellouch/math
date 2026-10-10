import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTransportPair

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistorySymbolicEncoding HistoryPairSmoothXi
open HistoryPairBulkTransport HistoryBulkSupportConversePlan HistoryBulkReferenceScalarCoordinates
open HistorySignedXiTransport HistoryGiantReferenceMean

section Pair
variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ)
  (s t : ℤ) (gp gm : ℕ) (P Q : ℤ)
  (x₀ x : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k₀) l).length))
  (hπ : ∀i, sources ((Template.current (Template.initial m k₀) l).get (π i)).origin =
    sources ((Template.current (Template.initial m k₀) l).get i).origin)
  (c e : HistoryChoices sources (Template.initial m k₀) V l)
local notation "T" => Template.current (Template.initial m k₀) l
local notation "H₀" => assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c
local notation "K₀" => assignedHistory sources (Template.initial m k₀) V l t gp gm
  (sourceAssignmentPermutation sources T π hπ x₀) e
local notation "H₁" => assignedHistory sources (Template.initial m k₀) V l s P.toNat Q.toNat x c
local notation "K₁" => assignedHistory sources (Template.initial m k₀) V l t P.toNat Q.toNat
  (sourceAssignmentPermutation sources T π hπ x) e

theorem integer_sourceIntegrand_transport (d : Decomposition) (hP : 0≤P) (hQ : 0≤Q)
    (hs : (H₀).Supported V outside) (ks : (K₀).Supported V outside)
    (hs' : (H₁).Supported V outside) (ks' : (K₁).Supported V outside)
    (hfixed : ∀i : Fin (T).length, ((T).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (J : ℤ→ℤ→ℂ) (bc sc : ℕ) (X tb td G : ℝ) :
    sourceIntegrand d sources (Template.initial m k₀) V outside l
      (sourceState sources T x s)
      (sourceState sources T (sourceAssignmentPermutation sources T π hπ x) t)
      c e J bc sc X tb td G P Q =
    J P Q * (((H₀).compensationProduct:ℂ)*((K₀).compensationProduct:ℂ))*
      pairedRealXi bc sc X tb td G H₀ K₀ hs ks
        (insertOrderedGiants m k₀ H₀ K₀ hs
          (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
          (orderedSourceValues sources m k₀ l x)
          (fun u => if u then (Q:ℝ) else (P:ℝ)))*
      ((H₁).leafProduct (spectatorFactor (residueTransform d) outside)*
        conj ((K₁).leafProduct (spectatorFactor (residueTransform d) outside))) := by
  have h := assigned_sourceIntegrand_transport sources m k₀ V outside l s t
    gp gm P.toNat Q.toNat x₀ x π hπ c e d hs ks hs' ks' hfixed J bc sc X tb td G
  have hPr : (P.toNat:ℝ)=(P:ℝ) := by
    rw [←Int.cast_natCast,Int.toNat_of_nonneg hP]
  have hQr : (Q.toNat:ℝ)=(Q:ℝ) := by
    rw [←Int.cast_natCast,Int.toNat_of_nonneg hQ]
  simpa only [Int.toNat_of_nonneg hP,Int.toNat_of_nonneg hQ,hPr,hQr] using h

end Pair
end Ostmann.Arithmetic.HistoryBulkFixedReferenceTransport

end

end OAI
