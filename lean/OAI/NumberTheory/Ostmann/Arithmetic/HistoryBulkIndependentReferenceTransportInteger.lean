import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransportPair

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransport
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistorySymbolicEncoding HistoryPairSmoothXi
open HistoryPairBulkTransport HistoryBulkSupportConversePlan HistoryBulkReferenceScalarCoordinates
open HistorySignedXiTransport HistoryGiantReferenceMean

section Pair
variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ)
  (s t : ℤ) (gp gm : ℕ) (P Q : ℤ)
  (x₀ y₀ x y : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k₀) l).length))
  (hold : ∀i, (y₀ i).val = (x₀ (π i)).val)
  (hnew : ∀i, (y i).val = (x (π i)).val)
  (c e : HistoryChoices sources (Template.initial m k₀) V l)
include hold hnew

theorem integer_sourceIntegrand_transport (d : Decomposition) (hP : 0≤P) (hQ : 0≤Q)
    (hs : ((assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c)).Supported V outside) (ks : ((assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e)).Supported V outside)
    (hs' : ((assignedHistory sources (Template.initial m k₀) V l s P.toNat Q.toNat x c)).Supported V outside) (ks' : ((assignedHistory sources (Template.initial m k₀) V l t P.toNat Q.toNat y e)).Supported V outside)
    (hfixed : ∀i : Fin ((Template.current (Template.initial m k₀) l)).length, (((Template.current (Template.initial m k₀) l)).get i).role≠.bulk → (x i).val=(x₀ i).val)
    (J : ℤ→ℤ→ℂ) (bc sc : ℕ) (X tb td G : ℝ) :
    sourceIntegrand d sources (Template.initial m k₀) V outside l
      (sourceState sources (Template.current (Template.initial m k₀) l) x s)
      (sourceState sources (Template.current (Template.initial m k₀) l) y t)
      c e J bc sc X tb td G P Q =
    J P Q * ((((assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c)).compensationProduct:ℂ)*(((assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e)).compensationProduct:ℂ))*
      pairedRealXi bc sc X tb td G (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs ks
        (insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs
          (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
          (orderedSourceValues sources m k₀ l x)
          (fun u => if u then (Q:ℝ) else (P:ℝ)))*
      (((assignedHistory sources (Template.initial m k₀) V l s P.toNat Q.toNat x c)).leafProduct (spectatorFactor (residueTransform d) outside)*
        conj (((assignedHistory sources (Template.initial m k₀) V l t P.toNat Q.toNat y e)).leafProduct (spectatorFactor (residueTransform d) outside))) := by
  have h := assigned_sourceIntegrand_transport sources m k₀ V outside l s t
    gp gm P.toNat Q.toNat x₀ y₀ x y π hold hnew c e d hs ks hs' ks' hfixed J bc sc X tb td G
  have hPr : (P.toNat:ℝ)=(P:ℝ) := by
    rw [←Int.cast_natCast,Int.toNat_of_nonneg hP]
  have hQr : (Q.toNat:ℝ)=(Q:ℝ) := by
    rw [←Int.cast_natCast,Int.toNat_of_nonneg hQ]
  simpa only [Int.toNat_of_nonneg hP,Int.toNat_of_nonneg hQ,hPr,hQr] using h

end Pair
end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransport

end

end OAI
